/* query.c - fork of the pinentry to query stuff from the user
 *	Copyright (C) 2001 Free Software Foundation, Inc.
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
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <unistd.h>
#include <sys/stat.h>

#include "agent.h"
#include "../assuan/assuan.h"

#ifdef _POSIX_OPEN_MAX
#define MAX_OPEN_FDS _POSIX_OPEN_MAX
#else
#define MAX_OPEN_FDS 20
#endif

static ASSUAN_CONTEXT entry_ctx = NULL;

/* data to be passed to our callbacks */
struct entry_parm_s {
  int lines;
  size_t size;
  char *buffer;
};




/* Fork off the pin entry if this has not already been done */
static int
start_pinentry (void)
{
  int rc;
  const char *pgmname;
  ASSUAN_CONTEXT ctx;
  const char *argv[3];

  if (entry_ctx)
    return 0; /* No need to serialize things becuase the agent is
                 expected to tun as a single-thread (or may be in
                 future using libpth) */


  log_debug ("no running PIN Entry - starting it\n");
      
  if (fflush (NULL))
    {
      log_error ("error flushing pending output: %s\n", strerror (errno));
      return seterr (Write_Error);
    }

  /* FIXME: change the default location of the program */
  if (!opt.pinentry_program || !*opt.pinentry_program)
    opt.pinentry_program = "../../pinentry/kpinentry/kpinentry";
  if ( !(pgmname = strrchr (opt.pinentry_program, '/')))
    pgmname = opt.pinentry_program;
  else
    pgmname++;

  argv[0] = pgmname;
  argv[1] = NULL;

  /* connect to the pinentry and perform initial handshaking */
  rc = assuan_pipe_connect (&ctx, opt.pinentry_program, (char**)argv, 0);
  if (rc)
    {
      log_error ("can't connect to the PIN entry module: %s\n",
                 assuan_strerror (rc));
      return seterr (No_PIN_Entry);
    }
  entry_ctx = ctx;
  
  log_debug ("connection to PIN entry established\n");

  rc = assuan_transact (entry_ctx, 
                        opt.no_grab? "OPTION no-grab":"OPTION grab",
                        NULL, NULL, NULL, NULL, NULL, NULL);
  if (rc)
    return map_assuan_err (rc);

  return 0;
}


static AssuanError
getpin_cb (void *opaque, const void *buffer, size_t length)
{
  struct entry_parm_s *parm = opaque;

  if (!buffer)
    return 0;

  /* we expect the pin to fit on one line */
  if (parm->lines || length >= parm->size)
    return ASSUAN_Too_Much_Data;

  /* fixme: we should make sure that the assuan buffer is allocated in
     secure memory or read the response byte by byte */
  memcpy (parm->buffer, buffer, length);
  parm->buffer[length] = 0;
  parm->lines++;
  return 0;
}


static int
all_digitsp( const char *s)
{
  for (; *s && *s >= '0' && *s <= '9'; s++)
    ;
  return !*s;
}  



/* Call the Entry and ask for the PIN.  We do check for a valid PIN
   number here and repeat it as long as we have invalid formed
   numbers. */
int
agent_askpin (const char *desc_text, const char *start_err_text,
              struct pin_entry_info_s *pininfo)
{
  int rc;
  char line[ASSUAN_LINELENGTH];
  struct entry_parm_s parm;
  const char *errtext = start_err_text;

  if (opt.batch)
    return 0; /* fixme: we should return BAD PIN */

  if (!pininfo || pininfo->max_length < 1)
    return seterr (Invalid_Value);
  if (!desc_text)
    desc_text = trans ("Please enter you PIN, so that the secret key "
                       "can be unlocked for this session");
  
  rc = start_pinentry ();
  if (rc)
    return rc;

  snprintf (line, DIM(line)-1, "SETDESC %s", desc_text);
  line[DIM(line)-1] = 0;
  rc = assuan_transact (entry_ctx, line, NULL, NULL, NULL, NULL, NULL, NULL);
  if (rc)
    return map_assuan_err (rc);

  rc = assuan_transact (entry_ctx,
                        pininfo->min_digits? "SETPROMPT PIN:"
                                           : "SETPROMPT Passphrase:",
                        NULL, NULL, NULL, NULL, NULL, NULL);
  if (rc)
    return map_assuan_err (rc);

  for (;pininfo->failed_tries < pininfo->max_tries; pininfo->failed_tries++)
    {
      memset (&parm, 0, sizeof parm);
      parm.size = pininfo->max_length;
      parm.buffer = pininfo->pin;

      if (errtext)
        { 
          /* fixme: should we show the try count? It must be translated */
          if (start_err_text)
            {
              snprintf (line, DIM(line)-1, "SETERROR %s", errtext);
              start_err_text = NULL;
            }
          else
            snprintf (line, DIM(line)-1, "SETERROR %s (try %d of %d)",
                      errtext, pininfo->failed_tries+1, pininfo->max_tries);
          line[DIM(line)-1] = 0;
          rc = assuan_transact (entry_ctx, line, NULL, NULL, NULL, NULL, NULL, NULL);
          if (rc)
            return map_assuan_err (rc);
          errtext = NULL;
        }
      
      rc = assuan_transact (entry_ctx, "GETPIN", getpin_cb, &parm, NULL, NULL, NULL, NULL);
      if (rc == ASSUAN_Too_Much_Data)
        errtext = pininfo->min_digits? trans ("PIN too long")
                                     : trans ("Passphrase too long");
      else if (rc)
        return map_assuan_err (rc);
      if (!errtext && !pininfo->min_digits)
        return 0; /* okay, got a passphrase */
      if (!errtext && !all_digitsp (pininfo->pin))
        errtext = trans ("Invalid characters in PIN");
      if (!errtext && pininfo->max_digits
          && strlen (pininfo->pin) > pininfo->max_digits)
        errtext = trans ("PIN too long");
      if (!errtext
          && strlen (pininfo->pin) < pininfo->min_digits)
        errtext = trans ("PIN too short");

      if (!errtext)
        return 0; /* okay, got a PIN */
    }

  return pininfo->min_digits? GNUPG_Bad_PIN : GNUPG_Bad_Passphrase;
}



/* Ask for the passphrase using the supplied arguments.  The
   passphrase is returned in RETPASS as an hex encoded string to be
   freed by the caller */
int 
agent_get_passphrase (char **retpass, const char *desc, const char *prompt,
                      const char *errtext)
{

  int rc;
  char line[ASSUAN_LINELENGTH];
  struct entry_parm_s parm;
  unsigned char *p, *hexstring;
  int i;

  *retpass = NULL;
  if (opt.batch)
    return GNUPG_Bad_Passphrase; 

  rc = start_pinentry ();
  if (rc)
    return rc;

  if (desc)
    snprintf (line, DIM(line)-1, "SETDESC %s", desc);
  else
    snprintf (line, DIM(line)-1, "RESET");
  line[DIM(line)-1] = 0;
  rc = assuan_transact (entry_ctx, line, NULL, NULL, NULL, NULL, NULL, NULL);
  if (rc)
    return map_assuan_err (rc);

  snprintf (line, DIM(line)-1, "SETPROMPT %s", prompt? prompt : "Passphrase");
  line[DIM(line)-1] = 0;
  rc = assuan_transact (entry_ctx, line, NULL, NULL, NULL, NULL, NULL, NULL);
  if (rc)
    return map_assuan_err (rc);

  if (errtext)
    {
      snprintf (line, DIM(line)-1, "SETERROR %s", errtext);
      line[DIM(line)-1] = 0;
      rc = assuan_transact (entry_ctx, line, NULL, NULL, NULL, NULL, NULL, NULL);
      if (rc)
        return map_assuan_err (rc);
    }

  memset (&parm, 0, sizeof parm);
  parm.size = ASSUAN_LINELENGTH/2 - 5;
  parm.buffer = gcry_malloc_secure (parm.size+10);
  if (!parm.buffer)
    return seterr (Out_Of_Core);

  assuan_begin_confidential (entry_ctx);
  rc = assuan_transact (entry_ctx, "GETPIN", getpin_cb, &parm, NULL, NULL, NULL, NULL);
  if (rc)
    {
      xfree (parm.buffer);
      return map_assuan_err (rc);
    }
  
  hexstring = gcry_malloc_secure (strlen (parm.buffer)*2+1);
  if (!hexstring)
    {
      xfree (parm.buffer);
      return seterr (Out_Of_Core);
    }

  for (i=0, p=parm.buffer; *p; p++, i += 2)
    sprintf (hexstring+i, "%02X", *p);
  
  xfree (parm.buffer);
  *retpass = hexstring;
  return 0;
}



/* Pop up the PIN-entry, display the text and the prompt and ask the
   user to confirm this.  We return 0 for success, ie. the used
   confirmed it, GNUPG_Not_Confirmed for what the text says or an
   other error. */
int 
agent_get_confirmation (const char *desc, const char *prompt)
{
  int rc;
  char line[ASSUAN_LINELENGTH];

  rc = start_pinentry ();
  if (rc)
    return rc;

  if (desc)
    snprintf (line, DIM(line)-1, "SETDESC %s", desc);
  else
    snprintf (line, DIM(line)-1, "RESET");
  line[DIM(line)-1] = 0;
  rc = assuan_transact (entry_ctx, line, NULL, NULL, NULL, NULL, NULL, NULL);
  if (rc)
    return map_assuan_err (rc);

  if (prompt)
    {
      snprintf (line, DIM(line)-1, "SETPROMPT %s", prompt);
      line[DIM(line)-1] = 0;
      rc = assuan_transact (entry_ctx, line, NULL, NULL, NULL, NULL, NULL, NULL);
      if (rc)
        return map_assuan_err (rc);
    }

  rc = assuan_transact (entry_ctx, "CONFIRM", NULL, NULL, NULL, NULL, NULL, NULL);
  return map_assuan_err (rc);
}



