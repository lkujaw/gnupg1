/* gpgkeys_http.c - fetch a key via HTTP
 * Copyright (C) 2004 Free Software Foundation, Inc.
 *
 * This file is part of GnuPG.
 *
 * GnuPG is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * GnuPG is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#include <config.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <unistd.h>
#ifdef HAVE_GETOPT_H
#include <getopt.h>
#endif
#define INCLUDED_BY_MAIN_MODULE 1
#include "util.h"
#include "http.h"
#include "keyserver.h"

extern char *optarg;
extern int optind;

#define GET    0
#define MAX_LINE 80

int verbose=0;
unsigned int http_flags=0;
char scheme[80]={'\0'},host[80]={'\0'},proxy[80]={'\0'},port[10]={'\0'},
  path[1024]={'\0'};
FILE *input=NULL,*output=NULL,*console=NULL;

#define BEGIN "-----BEGIN PGP PUBLIC KEY BLOCK-----"
#define END   "-----END PGP PUBLIC KEY BLOCK-----"

#ifdef __riscos__
#define HTTP_PROXY_ENV           "GnuPG$HttpProxy"
#else
#define HTTP_PROXY_ENV           "http_proxy"
#endif

static int
get_key(char *getkey)
{
  int rc,gotit=0;
  char *request;
  struct http_context hd;

  if(strncmp(getkey,"0x",2)==0)
    getkey+=2;

  fprintf(output,"KEY 0x%s BEGIN\n",getkey);

  if(verbose)
    fprintf(console,"gpgkeys: requesting key 0x%s from http://%s%s%s/%s\n",
	    getkey,host,port[0]?":":"",port[0]?port:"",path);

  request=malloc(strlen(scheme)+3+strlen(host)+1+strlen(port)+strlen(path)+99);
  if(!request)
    {
      fprintf(console,"gpgkeys: out of memory\n");
      return KEYSERVER_NO_MEMORY;
    }

  sprintf(request,"%s://%s%s%s%s",scheme,host,
	  port[0]?":":"",port[0]?port:"",path);

  if(verbose>2)
    fprintf(console,"gpgkeys: HTTP URL is \"%s\"\n",request);

  rc=http_open_document(&hd,request,http_flags,proxy[0]?proxy:NULL);
  if(rc!=0)
    {
      fprintf(console,"gpgkeys: HTTP fetch error: %s\n",
	      rc==G10ERR_NETWORK?strerror(errno):g10_errstr(rc));
      fprintf(output,"KEY 0x%s FAILED %d\n",getkey,
	    rc==G10ERR_NETWORK?KEYSERVER_UNREACHABLE:KEYSERVER_INTERNAL_ERROR);
    }
  else
    {
      unsigned int maxlen=1024,buflen;
      byte *line=NULL;

      while(iobuf_read_line(hd.fp_read,&line,&buflen,&maxlen))
	{
	  maxlen=1024;

	  if(gotit)
	    {
	      fputs (line, output);
	      if(strncmp(line,END,strlen(END))==0)
		break;
	    }
	  else
	    if(strncmp(line,BEGIN,strlen(BEGIN))==0)
	      {
		fputs (line,output);
		gotit=1;
	      }
	}

      if(gotit)
	fprintf(output,"KEY 0x%s END\n",getkey);
      else
	{
	  fprintf(console,"gpgkeys: key %s not found on keyserver\n",getkey);
	  fprintf(output,"KEY 0x%s FAILED %d\n",
		  getkey,KEYSERVER_KEY_NOT_FOUND);
	}

      m_free(line);
    }

  free(request);

  return KEYSERVER_OK;
}

int
main(int argc,char *argv[])
{
  int arg,action=-1,ret=KEYSERVER_INTERNAL_ERROR;
  char line[MAX_LINE];
  int failed=0;
  char *thekey=NULL;

  console=stderr;

  while((arg=getopt(argc,argv,"hVo:"))!=-1)
    switch(arg)
      {
      default:
      case 'h':
	fprintf(console,"-h\thelp\n");
	fprintf(console,"-V\tversion\n");
	fprintf(console,"-o\toutput to this file\n");
	return KEYSERVER_OK;

      case 'V':
	fprintf(stdout,"%d\n%s\n",KEYSERVER_PROTO_VERSION,VERSION);
	return KEYSERVER_OK;

      case 'o':
	output=fopen(optarg,"w");
	if(output==NULL)
	  {
	    fprintf(console,"gpgkeys: Cannot open output file \"%s\": %s\n",
		    optarg,strerror(errno));
	    return KEYSERVER_INTERNAL_ERROR;
	  }

	break;
      }

  if(argc>optind)
    {
      input=fopen(argv[optind],"r");
      if(input==NULL)
	{
	  fprintf(console,"gpgkeys: Cannot open input file \"%s\": %s\n",
		  argv[optind],strerror(errno));
	  return KEYSERVER_INTERNAL_ERROR;
	}
    }

  if(input==NULL)
    input=stdin;

  if(output==NULL)
    output=stdout;

  /* Get the command and info block */

  while(fgets(line,MAX_LINE,input)!=NULL)
    {
      int version;
      char commandstr[7];
      char optionstr[110];
      char hash;

      if(line[0]=='\n')
	break;

      if(sscanf(line,"%c",&hash)==1 && hash=='#')
	continue;

      if(sscanf(line,"COMMAND %6s\n",commandstr)==1)
	{
	  commandstr[6]='\0';

	  if(strcasecmp(commandstr,"get")==0)
	    action=GET;

	  continue;
	}

      if(sscanf(line,"SCHEME %79s\n",scheme)==1)
	{
	  scheme[79]='\0';
	  continue;
	}

      if(sscanf(line,"HOST %79s\n",host)==1)
	{
	  host[79]='\0';
	  continue;
	}

      if(sscanf(line,"PORT %9s\n",port)==1)
	{
	  port[9]='\0';
	  continue;
	}

      if(sscanf(line,"PATH %1023s\n",path)==1)
	{
	  path[1023]='\0';
	  continue;
	}

      if(sscanf(line,"VERSION %d\n",&version)==1)
	{
	  if(version!=KEYSERVER_PROTO_VERSION)
	    {
	      ret=KEYSERVER_VERSION_ERROR;
	      goto fail;
	    }

	  continue;
	}

      if(sscanf(line,"OPTION %109s\n",optionstr)==1)
	{
	  int no=0;
	  char *start=&optionstr[0];

	  optionstr[109]='\0';

	  if(strncasecmp(optionstr,"no-",3)==0)
	    {
	      no=1;
	      start=&optionstr[3];
	    }

	  if(strcasecmp(start,"verbose")==0)
	    {
	      if(no)
		verbose--;
	      else
		verbose++;
	    }
	  else if(strncasecmp(start,"http-proxy",10)==0)
	    {
	      if(no)
		proxy[0]='\0';
	      else if(start[10]=='=')
		{
		  strncpy(proxy,&start[11],79);
		  proxy[79]='\0';
		}
	      else if(start[10]=='\0')
		{
		  char *http_proxy=getenv(HTTP_PROXY_ENV);
		  if(http_proxy)
		    {
		      strncpy(proxy,http_proxy,79);
		      proxy[79]='\0';
		    }
		}
	    }
	  else if(strcasecmp(start,"broken-http-proxy")==0)
	    {
	      if(no)
		http_flags&=~HTTP_FLAG_NO_SHUTDOWN;
	      else
		http_flags|=HTTP_FLAG_NO_SHUTDOWN;
	    }
	  else if(strcasecmp(start,"try-dns-srv")==0)
	    {
	      if(no)
		http_flags&=~HTTP_FLAG_TRY_SRV;
	      else
		http_flags|=HTTP_FLAG_TRY_SRV;
	    }

	  continue;
	}
    }

  /* By suggested convention, if the user gives a :port, then disable
     SRV. */
  if(port[0])
    http_flags&=~HTTP_FLAG_TRY_SRV;

  /* If it's a GET or a SEARCH, the next thing to come in is the
     keyids.  If it's a SEND, then there are no keyids. */

  if(action==GET)
    {
      /* Eat the rest of the file */
      for(;;)
	{
	  if(fgets(line,MAX_LINE,input)==NULL)
	    break;
	  else
	    {
	      if(line[0]=='\n' || line[0]=='\0')
		break;

	      if(!thekey)
		{
		  thekey=strdup(line);
		  if(!thekey)
		    {
		      fprintf(console,"gpgkeys: out of memory while "
			      "building key list\n");
		      ret=KEYSERVER_NO_MEMORY;
		      goto fail;
		    }

		  /* Trim the trailing \n */
		  thekey[strlen(line)-1]='\0';
		}
	    }
	}
    }
  else
    {
      fprintf(console,
	      "gpgkeys: this keyserver type only supports key retrieval\n");
      goto fail;
    }

  /* Send the response */

  fprintf(output,"VERSION %d\n",KEYSERVER_PROTO_VERSION);
  fprintf(output,"PROGRAM %s\n\n",VERSION);

  if(verbose>1)
    {
      fprintf(console,"Scheme:\t\t%s\n",scheme);
      fprintf(console,"Host:\t\t%s\n",host);
      if(port[0])
	fprintf(console,"Port:\t\t%s\n",port);
      if(path[0])
	fprintf(console,"Path:\t\t%s\n",path);
      fprintf(console,"Command:\tGET\n");
    }

  if(get_key(thekey)!=KEYSERVER_OK)
    failed++;

  if(!failed)
    ret=KEYSERVER_OK;

 fail:

  free(thekey);

  if(input!=stdin)
    fclose(input);

  if(output!=stdout)
    fclose(output);

  return ret;
}