/* g10.c - The GNUPG utility (main for gpg)
 *	Copyright (C) 1998 Free Software Foundation, Inc.
 *
 * This file is part of GNUPG.
 *
 * GNUPG is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * GNUPG is distributed in the hope that it will be useful,
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
#include <unistd.h>

/* #define MAINTAINER_OPTIONS */

#include "packet.h"
#include "iobuf.h"
#include "memory.h"
#include "util.h"
#include "main.h"
#include "options.h"
#include "keydb.h"
#include "mpi.h"
#include "cipher.h"
#include "filter.h"
#include "trustdb.h"
#include "ttyio.h"
#include "i18n.h"
#include "status.h"

#ifndef IS_G10MAINT
  #define IS_G10 1
#endif


enum cmd_and_opt_values { aNull = 0,
    oArmor	  = 'a',
    aDetachedSign = 'b',
    aSym	  = 'c',
    aDecrypt	  = 'd',
    aEncr	  = 'e',
    oKOption	  = 'k',
    oDryRun	  = 'n',
    oOutput	  = 'o',
    oRemote	  = 'r',
    aSign	  = 's',
    oTextmode	  = 't',
    oUser	  = 'u',
    oVerbose	  = 'v',
    oCompress	  = 'z',
    oBatch	  = 500,
    aClearsign,
    aStore,
    aKeygen,
    aSignEncr,
    aSignKey,
    aListPackets,
    aEditKey,
    aDeleteKey,
    aDeleteSecretKey,
    aKMode,
    aKModeC,
    aImport,
    aVerify,
    aListKeys,
    aListSigs,
    aListSecretKeys,
    aExport,
    aExportSecret,
    aCheckKeys,
    aGenRevoke,
    aPrimegen,
    aPrintMD,
    aPrintMDs,
    aCheckTrustDB,
    aListTrustDB,
    aListTrustPath,
    aExportOwnerTrust,
    aImportOwnerTrust,
    aDeArmor,
    aEnArmor,
    aGenRandom,

    oFingerprint,
    oDoNotExportRSA,
    oAnswerYes,
    oAnswerNo,
    oKeyring,
    oSecretKeyring,
    oDefaultKey,
    oOptions,
    oDebug,
    oDebugAll,
    oStatusFD,
    oNoComment,
    oCompletesNeeded,
    oMarginalsNeeded,
    oLoadExtension,
    oRFC1991,
    oCipherAlgo,
    oDigestAlgo,
    oCompressAlgo,
    oPasswdFD,
    oQuickRandom,
    oNoVerbose,
    oTrustDBName,
    oNoSecmemWarn,
    oNoArmor,
    oNoDefKeyring,
    oNoGreeting,
    oNoOptions,
    oNoBatch,
    oHomedir,
    oWithColons,
    oSkipVerify,
    oCompressKeys,
    oCompressSigs,
    oAlwaysTrust,
    oEmuChecksumBug,
    oRunAsShmCP,
    oSetFilename,
    oComment,
    oThrowKeyid,
    oS2KMode,
    oS2KDigest,
    oS2KCipher,
aTest };


static ARGPARSE_OPTS opts[] = {

    { 300, NULL, 0, N_("@Commands:\n ") },

  #ifdef IS_G10
    { aSign, "sign",      256, N_("|[file]|make a signature")},
    { aClearsign, "clearsign", 256, N_("|[file]|make a clear text signature") },
    { aDetachedSign, "detach-sign", 256, N_("make a detached signature")},
    { aEncr, "encrypt",   256, N_("encrypt data")},
    { aSym, "symmetric", 256, N_("encryption only with symmetric cipher")},
    { aStore, "store",     256, N_("store only")},
    { aDecrypt, "decrypt",   256, N_("decrypt data (default)")},
    { aVerify, "verify"   , 256, N_("verify a signature")},
  #endif
    { aListKeys, "list-keys", 256, N_("list keys")},
    { aListSigs, "list-sigs", 256, N_("list keys and signatures")},
    { aCheckKeys, "check-sigs",256, N_("check key signatures")},
    { oFingerprint, "fingerprint", 256, N_("list keys and fingerprints")},
    { aListSecretKeys, "list-secret-keys", 256, N_("list secret keys")},
  #ifdef IS_G10
    { aKeygen, "gen-key",   256, N_("generate a new key pair")},
  #endif
    { aDeleteKey, "delete-key",256, N_("remove key from the public keyring")},
  #ifdef IS_G10
    { aEditKey, "edit-key"  ,256, N_("sign or edit a key")},
    { aGenRevoke, "gen-revoke",256, N_("generate a revocation certificate")},
  #endif
    { aExport, "export"          , 256, N_("export keys") },
    { aExportSecret, "export-secret-keys" , 256, "@" },
    { oDoNotExportRSA, "do-not-export-rsa", 0, "@" },
    { aImport, "import",      256     , N_("import/merge keys")},
    { aListPackets, "list-packets",256,N_("list only the sequence of packets")},
  #ifdef IS_G10MAINT
    { aExportOwnerTrust, "export-ownertrust", 256, N_("export the ownertrust values")},
    { aImportOwnerTrust, "import-ownertrust", 256 , N_("import ownertrust values")},
    { aCheckTrustDB, "check-trustdb",0 , N_("|[NAMES]|check the trust database")},
    { aDeArmor, "dearmor", 256, N_("De-Armor a file or stdin") },
    { aEnArmor, "enarmor", 256, N_("En-Armor a file or stdin") },
    { aPrintMD,  "print-md" , 256, N_("|algo [files]|print message digests")},
    { aPrintMDs, "print-mds" , 256, N_("print all message digests")},
    #ifdef MAINTAINER_OPTIONS
    { aPrimegen, "gen-prime" , 256, "@" },
    { aGenRandom, "gen-random" , 256, "@" },
    #endif
  #endif

    { 301, NULL, 0, N_("@\nOptions:\n ") },

    { oArmor, "armor",     0, N_("create ascii armored output")},
  #ifdef IS_G10
    { oUser, "local-user",2, N_("use this user-id to sign or decrypt")},
    { oRemote, "remote-user", 2, N_("use this user-id for encryption")},
    { oCompress, NULL,	      1, N_("|N|set compress level N (0 disables)") },
    { oTextmode, "textmode",  0, N_("use canonical text mode")},
  #endif
    { oOutput, "output",    2, N_("use as output file")},
    { oVerbose, "verbose",   0, N_("verbose") },
 /* { oDryRun, "dry-run",   0, N_("do not make any changes") }, */
    { oBatch, "batch",     0, N_("batch mode: never ask")},
    { oAnswerYes, "yes",       0, N_("assume yes on most questions")},
    { oAnswerNo,  "no",        0, N_("assume no on most questions")},
    { oKeyring, "keyring"   ,2, N_("add this keyring to the list of keyrings")},
    { oSecretKeyring, "secret-keyring" ,2, N_("add this secret keyring to the list")},
    { oDefaultKey, "default-key" ,2, N_("|NAME|use NAME as default secret key")},
    { oOptions, "options"   , 2, N_("read options from file")},

    { oDebug, "debug"     ,4|16, N_("set debugging flags")},
    { oDebugAll, "debug-all" ,0, N_("enable full debugging")},
    { oStatusFD, "status-fd" ,1, N_("|FD|write status info to this FD") },
    { oNoComment, "no-comment", 0,   N_("do not write comment packets")},
    { oCompletesNeeded, "completes-needed", 1, N_("(default is 1)")},
    { oMarginalsNeeded, "marginals-needed", 1, N_("(default is 3)")},
    { oLoadExtension, "load-extension" ,2, N_("|file|load extension module")},
    { oRFC1991, "rfc1991",   0, N_("emulate the mode described in RFC1991")},
    { oS2KMode, "s2k-mode",  1, N_("|N|use passphrase mode N")},
    { oS2KDigest, "s2k-digest-algo",2,
		N_("|NAME|use message digest algorithm NAME for passphrases")},
    { oS2KCipher, "s2k-cipher-algo",2,
		N_("|NAME|use cipher algorithm NAME for passphrases")},
  #ifdef IS_G10
    { oCipherAlgo, "cipher-algo", 2 , N_("|NAME|use cipher algorithm NAME")},
    { oDigestAlgo, "digest-algo", 2 , N_("|NAME|use message digest algorithm NAME")},
    { oCompressAlgo, "compress-algo", 1 , N_("|N|use compress algorithm N")},
    { oThrowKeyid, "throw-keyid", 0, N_("throw keyid field of encrypted packets")},
  #else /* some dummies */
    { oCipherAlgo, "cipher-algo", 2 , "@"},
    { oDigestAlgo, "digest-algo", 2 , "@"},
    { oCompressAlgo, "compress-algo", 1 , "@"},
  #endif

  #ifdef IS_G10
    { 302, NULL, 0, N_("@\nExamples:\n\n"
    " -se -r Bob [file]          sign and encrypt for user Bob\n"
    " --clearsign [file]         make a clear text signature\n"
    " --detach-sign [file]       make a detached signature\n"
    " --list-keys [names]        show keys\n"
    " --fingerprint [names]      show fingerprints\n"  ) },
  #endif

  /* hidden options */
  #ifdef IS_G10MAINT
    { aTest, "test"      , 0, "@" },
    { aExportOwnerTrust, "list-ownertrust",0 , "@"},  /* alias */
    { aListTrustDB, "list-trustdb",0 , "@"},
    { aListTrustPath, "list-trust-path",0, "@"},
  #endif
  #ifdef IS_G10
    { oKOption, NULL,	 0, "@"},
    { aEditKey, "edit-sig"  ,0, "@"}, /* alias for edit-key */
    { oPasswdFD, "passphrase-fd",1, "@" },
    { aSignKey, "sign-key"  ,256, "@" }, /* alias for edit-key */
  #endif
    { aDeleteSecretKey, "delete-secret-key",0, "@" },
    { oQuickRandom, "quick-random", 0, "@"},
    { oNoVerbose, "no-verbose", 0, "@"},
    { oTrustDBName, "trustdb-name", 2, "@" },
    { oNoSecmemWarn, "no-secmem-warning", 0, "@" }, /* used only by regression tests */
    { oNoArmor, "no-armor",   0, "@"},
    { oNoDefKeyring, "no-default-keyring", 0, "@" },
    { oNoGreeting, "no-greeting", 0, "@" },
    { oNoOptions, "no-options", 0, "@" }, /* shortcut for --options /dev/null */
    { oHomedir, "homedir", 2, "@" },   /* defaults to "~/.gnupg" */
    { oNoBatch, "no-batch", 0, "@" },
    { oWithColons, "with-colons", 0, "@"},
    { aListKeys, "list-key", 0, "@" }, /* alias */
    { aListSigs, "list-sig", 0, "@" }, /* alias */
    { aCheckKeys, "check-sig",0, "@" }, /* alias */
    { oSkipVerify, "skip-verify",0, "@" },
    { oCompressKeys, "compress-keys",0, "@"},
    { oCompressSigs, "compress-sigs",0, "@"},
    { oAlwaysTrust, "always-trust", 0, "@"},
    { oEmuChecksumBug, "emulate-checksum-bug", 0, "@"},
    { oRunAsShmCP, "run-as-shm-coprocess", 4, "@" },
    { oSetFilename, "set-filename", 2, "@" },
    { oComment, "comment", 2, "@" },
{0} };



static int maybe_setuid = 1;

static char *build_list( const char *text,
			 const char *(*mapf)(int), int (*chkf)(int) );
static void set_cmd( enum cmd_and_opt_values *ret_cmd,
			enum cmd_and_opt_values new_cmd );
#ifdef IS_G10MAINT
static void print_hex( byte *p, size_t n );
static void print_mds( const char *fname, int algo );
#endif

const char *
strusage( int level )
{
  static char *digests, *pubkeys, *ciphers;
    const char *p;
    switch( level ) {
      case 11: p =
	  #ifdef IS_G10MAINT
	    "gpgm (GNUPG)";
	  #else
	    "gpg (GNUPG)";
	  #endif
	break;
      case 13: p = VERSION; break;
      case 17: p = PRINTABLE_OS_NAME; break;
      case 19: p =
	    _("Please report bugs to <gnupg-bugs@gnu.org>.\n");
	break;
      case 1:
      case 40:	p =
	  #ifdef IS_G10MAINT
	    _("Usage: gpgm [options] [files] (-h for help)");
	  #else
	    _("Usage: gpg [options] [files] (-h for help)");
	  #endif
	break;
      case 41:	p =
	  #ifdef IS_G10MAINT
	    _("Syntax: gpgm [options] [files]\n"
	      "GNUPG maintenance utility\n");
	  #else
	    _("Syntax: gpg [options] [files]\n"
	      "sign, check, encrypt or decrypt\n"
	      "default operation depends on the input data\n");
	  #endif
	break;

      case 31: p = _("\nSupported algorithms:\n"); break;
      case 32:
	if( !ciphers )
	    ciphers = build_list("Cipher: ", cipher_algo_to_string,
							check_cipher_algo );
	p = ciphers;
	break;
      case 33:
	if( !pubkeys )
	    pubkeys = build_list("Pubkey: ", pubkey_algo_to_string,
							check_pubkey_algo );
	p = pubkeys;
	break;
      case 34:
	if( !digests )
	    digests = build_list("Hash: ", digest_algo_to_string,
							check_digest_algo );
	p = digests;
	break;

      default:	p = default_strusage(level);
    }
    return p;
}


static char *
build_list( const char *text, const char * (*mapf)(int), int (*chkf)(int) )
{
    int i;
    const char *s;
    size_t n=strlen(text)+2;
    char *list, *p;

    if( maybe_setuid )
	secmem_init( 0 );    /* drop setuid */

    for(i=1; i < 110; i++ )
	if( !chkf(i) && (s=mapf(i)) )
	    n += strlen(s) + 2;
    list = m_alloc( 21 + n ); *list = 0;
    for(p=NULL, i=1; i < 110; i++ ) {
	if( !chkf(i) && (s=mapf(i)) ) {
	    if( !p )
		p = stpcpy( list, text );
	    else
		p = stpcpy( p, ", ");
	    p = stpcpy(p, s );
	}
    }
    if( p )
	p = stpcpy(p, "\n" );
    return list;
}


static void
i18n_init(void)
{
  #ifdef ENABLE_NLS
    #ifdef HAVE_LC_MESSAGES
       setlocale( LC_TIME, "" );
       setlocale( LC_MESSAGES, "" );
    #else
       setlocale( LC_ALL, "" );
    #endif
    bindtextdomain( PACKAGE, G10_LOCALEDIR );
    textdomain( PACKAGE );
  #endif
}

static void
wrong_args( const char *text)
{
  #ifdef IS_G10MAINT
    fputs(_("usage: gpgm [options] "),stderr);
  #else
    fputs(_("usage: gpg [options] "),stderr);
  #endif
    fputs(text,stderr);
    putc('\n',stderr);
    g10_exit(2);
}

static void
set_debug(void)
{
    if( opt.debug & DBG_MEMORY_VALUE )
	memory_debug_mode = 1;
    if( opt.debug & DBG_MEMSTAT_VALUE )
	memory_stat_debug_mode = 1;
    if( opt.debug & DBG_MPI_VALUE )
	mpi_debug_mode = 1;
    if( opt.debug & DBG_CIPHER_VALUE )
	g10c_debug_mode = 1;
    if( opt.debug & DBG_IOBUF_VALUE )
	iobuf_debug_mode = 1;

}


static void
set_cmd( enum cmd_and_opt_values *ret_cmd, enum cmd_and_opt_values new_cmd )
{
    enum cmd_and_opt_values cmd = *ret_cmd;

    if( !cmd || cmd == new_cmd )
	cmd = new_cmd;
    else if( cmd == aSign && new_cmd == aEncr )
	cmd = aSignEncr;
    else if( cmd == aEncr && new_cmd == aSign )
	cmd = aSignEncr;
    else if( cmd == aKMode && new_cmd == aSym )
	cmd = aKModeC;
    else if(	( cmd == aSign	   && new_cmd == aClearsign )
	     || ( cmd == aClearsign && new_cmd == aSign )  )
	cmd = aClearsign;
    else {
	log_error(_("conflicting commands\n"));
	g10_exit(2);
    }

    *ret_cmd = cmd;
}



int
main( int argc, char **argv )
{
    ARGPARSE_ARGS pargs;
    IOBUF a;
    int rc=0;
    int orig_argc;
    char **orig_argv;
    const char *fname;
    STRLIST sl, remusr= NULL, locusr=NULL;
    STRLIST nrings=NULL, sec_nrings=NULL;
    armor_filter_context_t afx;
    int detached_sig = 0;
    FILE *configfp = NULL;
    char *configname = NULL;
    unsigned configlineno;
    int parse_debug = 0;
    int default_config =1;
    int errors=0;
    int default_keyring = 1;
    int greeting = 1;
    enum cmd_and_opt_values cmd = 0;
    const char *trustdb_name = NULL;
    char *def_cipher_string = NULL;
    char *def_digest_string = NULL;
    char *s2k_cipher_string = NULL;
    char *s2k_digest_string = NULL;
    int pwfd = -1;
  #ifdef USE_SHM_COPROCESSING
    ulong requested_shm_size=0;
  #endif

    trap_unaligned();
    secmem_set_flags( secmem_get_flags() | 2 ); /* suspend warnings */
  #ifdef IS_G10MAINT
    secmem_init( 0 );	   /* disable use of secmem */
    maybe_setuid = 0;
    log_set_name("gpgm");
  #else
    /* Please note that we may running SUID(ROOT), so be very CAREFUL
     * when adding any stuff between here and the call to
     * secmem_init()  somewhere after the option parsing
     */
    log_set_name("gpg");
    secure_random_alloc(); /* put random number into secure memory */
    disable_core_dumps();
    init_signals();
  #endif
    i18n_init();
    opt.compress = -1; /* defaults to standard compress level */
    /* fixme: set the next two to zero and decide where used */
    opt.def_cipher_algo = 0;
    opt.def_digest_algo = 0;
    opt.def_compress_algo = 2;
    opt.s2k_mode = 1; /* salted */
    opt.s2k_digest_algo = DIGEST_ALGO_RMD160;
    opt.s2k_cipher_algo = CIPHER_ALGO_BLOWFISH;
    opt.completes_needed = 1;
    opt.marginals_needed = 3;
    opt.homedir = getenv("GNUPGHOME");
    if( !opt.homedir || !*opt.homedir ) {
      #ifdef __MINGW32__
	opt.homedir = "c:/gnupg";
      #else
	opt.homedir = "~/.gnupg";
      #endif
    }

    /* check whether we have a config file on the commandline */
    orig_argc = argc;
    orig_argv = argv;
    pargs.argc = &argc;
    pargs.argv = &argv;
    pargs.flags= 1|(1<<6);  /* do not remove the args, ignore version */
    while( arg_parse( &pargs, opts) ) {
	if( pargs.r_opt == oDebug || pargs.r_opt == oDebugAll )
	    parse_debug++;
	else if( pargs.r_opt == oOptions ) {
	    /* yes there is one, so we do not try the default one, but
	     * read the option file when it is encountered at the commandline
	     */
	    default_config = 0;
	}
	else if( pargs.r_opt == oNoOptions )
	    default_config = 0; /* --no-options */
	else if( pargs.r_opt == oHomedir )
	    opt.homedir = pargs.r.ret_str;
      #ifdef USE_SHM_COPROCESSING
	else if( pargs.r_opt == oRunAsShmCP ) {
	    /* does not make sense in a options file, we do it here,
	     * so that we are the able to drop setuid as soon as possible */
	    opt.shm_coprocess = 1;
	    requested_shm_size = pargs.r.ret_ulong;
	}
      #endif
    }


  #ifdef USE_SHM_COPROCESSING
    if( opt.shm_coprocess ) {
      #ifdef IS_G10
	init_shm_coprocessing(requested_shm_size, 1 );
      #else
	init_shm_coprocessing(requested_shm_size, 0 );
      #endif
    }
  #endif
  #ifdef IS_G10
    /* initialize the secure memory. */
    secmem_init( 16384 );
    maybe_setuid = 0;
    /* Okay, we are now working under our real uid */
  #endif


    if( default_config )
	configname = make_filename(opt.homedir, "options", NULL );

    argc = orig_argc;
    argv = orig_argv;
    pargs.argc = &argc;
    pargs.argv = &argv;
    pargs.flags=  1;  /* do not remove the args */
  next_pass:
    if( configname ) {
	configlineno = 0;
	configfp = fopen( configname, "r" );
	if( !configfp ) {
	    if( default_config ) {
		if( parse_debug )
		    log_info(_("note: no default option file '%s'\n"),
							    configname );
	    }
	    else {
		log_error(_("option file '%s': %s\n"),
				    configname, strerror(errno) );
		g10_exit(2);
	    }
	    m_free(configname); configname = NULL;
	}
	if( parse_debug && configname )
	    log_info(_("reading options from '%s'\n"), configname );
	default_config = 0;
    }

    while( optfile_parse( configfp, configname, &configlineno,
						&pargs, opts) ) {
	switch( pargs.r_opt ) {
	  case aCheckKeys: set_cmd( &cmd, aCheckKeys); break;
	  case aListPackets: set_cmd( &cmd, aListPackets); break;
	  case aImport: set_cmd( &cmd, aImport); break;
	  case aExport: set_cmd( &cmd, aExport); break;
	  case aListKeys: set_cmd( &cmd, aListKeys); break;
	  case aListSigs: set_cmd( &cmd, aListSigs); break;
	  case aExportSecret: set_cmd( &cmd, aExportSecret); break;
	  case aDeleteSecretKey: set_cmd( &cmd, aDeleteSecretKey); break;
	  case aDeleteKey: set_cmd( &cmd, aDeleteKey); break;

	#ifdef IS_G10
	  case aDetachedSign: detached_sig = 1; set_cmd( &cmd, aSign ); break;
	  case aSym: set_cmd( &cmd, aSym); break;
	  case aDecrypt: set_cmd( &cmd, aDecrypt); break;
	  case aEncr: set_cmd( &cmd, aEncr); break;
	  case aSign: set_cmd( &cmd, aSign );  break;
	  case aKeygen: set_cmd( &cmd, aKeygen); break;
	  case aSignKey: set_cmd( &cmd, aSignKey); break;
	  case aStore: set_cmd( &cmd, aStore); break;
	  case aEditKey: set_cmd( &cmd, aEditKey); break;
	  case aClearsign: set_cmd( &cmd, aClearsign); break;
	  case aGenRevoke: set_cmd( &cmd, aGenRevoke); break;
	  case aVerify: set_cmd( &cmd, aVerify); break;
	#else
	  #ifdef MAINTAINER_OPTIONS
	    case aPrimegen: set_cmd( &cmd, aPrimegen); break;
	    case aTest: set_cmd( &cmd, aTest); break;
	    case aGenRandom: set_cmd( &cmd, aGenRandom); break;
	  #endif
	  case aPrintMD: set_cmd( &cmd, aPrintMD); break;
	  case aPrintMDs: set_cmd( &cmd, aPrintMDs); break;
	  case aListTrustDB: set_cmd( &cmd, aListTrustDB); break;
	  case aCheckTrustDB: set_cmd( &cmd, aCheckTrustDB); break;
	  case aListTrustPath: set_cmd( &cmd, aListTrustPath); break;
	  case aDeArmor: set_cmd( &cmd, aDeArmor); break;
	  case aEnArmor: set_cmd( &cmd, aEnArmor); break;
	  case aExportOwnerTrust: set_cmd( &cmd, aExportOwnerTrust); break;
	  case aImportOwnerTrust: set_cmd( &cmd, aImportOwnerTrust); break;
	#endif /* IS_G10MAINT */



	  case oArmor: opt.armor = 1; opt.no_armor=0; break;
	  case oOutput: opt.outfile = pargs.r.ret_str; break;
	  case oVerbose: g10_opt_verbose++;
		    opt.verbose++; opt.list_sigs=1; break;
	  case oKOption: set_cmd( &cmd, aKMode ); break;

	  case oBatch: opt.batch = 1; greeting = 0; break;
	  case oAnswerYes: opt.answer_yes = 1; break;
	  case oAnswerNo: opt.answer_no = 1; break;
	  case oKeyring: append_to_strlist( &nrings, pargs.r.ret_str); break;
	  case oDebug: opt.debug |= pargs.r.ret_ulong; break;
	  case oDebugAll: opt.debug = ~0; break;
	  case oStatusFD: set_status_fd( pargs.r.ret_int ); break;
	  case oFingerprint: opt.fingerprint++; break;
	  case oSecretKeyring: append_to_strlist( &sec_nrings, pargs.r.ret_str); break;
	  case oOptions:
	    /* config files may not be nested (silently ignore them) */
	    if( !configfp ) {
		m_free(configname);
		configname = m_strdup(pargs.r.ret_str);
		goto next_pass;
	    }
	    break;
	  case oNoArmor: opt.no_armor=1; opt.armor=0; break;
	  case oNoDefKeyring: default_keyring = 0; break;
	  case oNoGreeting: greeting = 0; break;
	  case oNoVerbose: g10_opt_verbose = 0;
			   opt.verbose = 0; opt.list_sigs=0; break;
	  case oQuickRandom: quick_random_gen(1); break;
	  case oNoComment: opt.no_comment=1; break;
	  case oCompletesNeeded: opt.completes_needed = pargs.r.ret_int; break;
	  case oMarginalsNeeded: opt.marginals_needed = pargs.r.ret_int; break;
	  case oTrustDBName: trustdb_name = pargs.r.ret_str; break;
	  case oDefaultKey: opt.def_secret_key = pargs.r.ret_str; break;
	  case oNoOptions: break; /* no-options */
	  case oHomedir: opt.homedir = pargs.r.ret_str; break;
	  case oNoBatch: opt.batch = 0; break;
	  case oWithColons: opt.with_colons=':'; break;

	  case oSkipVerify: opt.skip_verify=1; break;
	  case oCompressAlgo: opt.def_compress_algo = pargs.r.ret_int; break;
	  case oCompressKeys: opt.compress_keys = 1; break;
	  case aListSecretKeys: set_cmd( &cmd, aListSecretKeys); break;
	  case oAlwaysTrust: opt.always_trust = 1; break;
	  case oLoadExtension: register_cipher_extension(pargs.r.ret_str); break;
	  case oRFC1991: opt.rfc1991 = 1; opt.no_comment = 1; break;
	  case oEmuChecksumBug: opt.emulate_bugs |= EMUBUG_GPGCHKSUM; break;
	  case oDoNotExportRSA: opt.do_not_export_rsa = 1; break;
	  case oCompressSigs: opt.compress_sigs = 1; break;
	  case oRunAsShmCP:
	  #ifndef USE_SHM_COPROCESSING
	    /* not possible in the option file,
	     * but we print the warning here anyway */
	    log_error("shared memory coprocessing is not available\n");
	  #endif
	    break;
	  case oSetFilename: opt.set_filename = pargs.r.ret_str; break;
	  case oComment: opt.comment_string = pargs.r.ret_str; break;
	  case oThrowKeyid: opt.throw_keyid = 1; break;
	  case oS2KMode:   opt.s2k_mode = pargs.r.ret_int; break;
	  case oS2KDigest: s2k_digest_string = m_strdup(pargs.r.ret_str); break;
	  case oS2KCipher: s2k_cipher_string = m_strdup(pargs.r.ret_str); break;

	#ifdef IS_G10
	  case oRemote: /* store the remote users */
	    sl = m_alloc( sizeof *sl + strlen(pargs.r.ret_str));
	    strcpy(sl->d, pargs.r.ret_str);
	    sl->next = remusr;
	    remusr = sl;
	    break;
	  case oTextmode: opt.textmode=1;  break;
	  case oUser: /* store the local users */
	    sl = m_alloc( sizeof *sl + strlen(pargs.r.ret_str));
	    strcpy(sl->d, pargs.r.ret_str);
	    sl->next = locusr;
	    locusr = sl;
	    break;
	  case oCompress: opt.compress = pargs.r.ret_int; break;
	  case oPasswdFD: pwfd = pargs.r.ret_int; break;
	  case oCipherAlgo: def_cipher_string = m_strdup(pargs.r.ret_str); break;
	  case oDigestAlgo: def_digest_string = m_strdup(pargs.r.ret_str); break;
	  case oNoSecmemWarn: secmem_set_flags( secmem_get_flags() | 1 ); break;
	#else
	  case oCipherAlgo:
	  case oDigestAlgo:
	  case oNoSecmemWarn:
	    break;  /* dummies */
	#endif

	  default : errors++; pargs.err = configfp? 1:2; break;
	}
    }
    if( configfp ) {
	fclose( configfp );
	configfp = NULL;
	m_free(configname); configname = NULL;
	goto next_pass;
    }
    m_free( configname ); configname = NULL;
    if( log_get_errorcount(0) )
	g10_exit(2);

    if( greeting ) {
	tty_printf("%s %s; %s\n", strusage(11), strusage(13), strusage(14) );
	tty_printf("%s\n", strusage(15) );
    }

    secmem_set_flags( secmem_get_flags() & ~2 ); /* resume warnings */

    set_debug();

    /* must do this after dropping setuid, because string_to...
     * may try to load an module */
    if( def_cipher_string ) {
	opt.def_cipher_algo = string_to_cipher_algo(def_cipher_string);
	m_free(def_cipher_string); def_cipher_string = NULL;
	if( check_cipher_algo(opt.def_cipher_algo) )
	    log_error(_("selected cipher algorithm is invalid\n"));
    }
    if( def_digest_string ) {
	opt.def_digest_algo = string_to_digest_algo(def_digest_string);
	m_free(def_digest_string); def_digest_string = NULL;
	if( check_digest_algo(opt.def_digest_algo) )
	    log_error(_("selected digest algorithm is invalid\n"));
    }
    if( s2k_cipher_string ) {
	opt.s2k_cipher_algo = string_to_cipher_algo(s2k_cipher_string);
	m_free(s2k_cipher_string); s2k_cipher_string = NULL;
	if( check_cipher_algo(opt.s2k_cipher_algo) )
	    log_error(_("selected cipher algorithm is invalid\n"));
    }
    if( s2k_digest_string ) {
	opt.s2k_digest_algo = string_to_digest_algo(s2k_digest_string);
	m_free(s2k_digest_string); s2k_digest_string = NULL;
	if( check_digest_algo(opt.s2k_digest_algo) )
	    log_error(_("selected digest algorithm is invalid\n"));
    }
    if( opt.def_compress_algo < 1 || opt.def_compress_algo > 2 )
	log_error(_("compress algorithm must be in range %d..%d\n"), 1, 2);
    if( opt.completes_needed < 1 )
	log_error(_("completes-needed must be greater than 0\n"));
    if( opt.marginals_needed < 2 )
	log_error(_("marginals-needed must be greater than 1\n"));
    switch( opt.s2k_mode ) {
      case 0:
	log_info(_("note: simple S2K mode (0) is strongly discouraged\n"));
	break;
      case 1: case 3: break;
      default:
	log_error(_("invalid S2K mode; must be 0, 1 or 3\n"));
    }

    if( log_get_errorcount(0) )
	g10_exit(2);

    if( !cmd && opt.fingerprint )
	set_cmd( &cmd, aListKeys);

    if( cmd == aKMode || cmd == aKModeC ) { /* kludge to be compatible to pgp */
	if( cmd == aKModeC ) {
	    opt.fingerprint = 1;
	    cmd = aKMode;
	}
	opt.list_sigs = 0;
	if( opt.verbose > 2 )
	    opt.check_sigs++;
	if( opt.verbose > 1 )
	    opt.list_sigs++;

	opt.verbose = opt.verbose > 1;
	g10_opt_verbose = opt.verbose;
    }


    /* kludge to let -sat generate a clear text signature */
    if( opt.textmode && !detached_sig && opt.armor && cmd == aSign )
	cmd = aClearsign;

    if( opt.verbose > 1 )
	set_packet_list_mode(1);

    /* add the keyrings, but not for some special commands and
     * not in case of "-kvv userid keyring" */
    if( cmd != aDeArmor && cmd != aEnArmor
	&& !(cmd == aKMode && argc == 2 ) ) {

	if( !sec_nrings || default_keyring )  /* add default secret rings */
	    add_secret_keyring("secring.gpg");
	for(sl = sec_nrings; sl; sl = sl->next )
	    add_secret_keyring( sl->d );
	if( !nrings || default_keyring )  /* add default ring */
	    add_keyring("pubring.gpg");
	for(sl = nrings; sl; sl = sl->next )
	    add_keyring( sl->d );
    }
    FREE_STRLIST(nrings);
    FREE_STRLIST(sec_nrings);


    if( pwfd != -1 )  /* read the passphrase now. */
	read_passphrase_from_fd( pwfd );

    fname = argc? *argv : NULL;

    switch( cmd ) {
      case aPrimegen:
      case aPrintMD:
      case aPrintMDs:
      case aGenRandom:
      case aDeArmor:
      case aEnArmor:
	break;
      case aKMode:
      case aListKeys:
      case aListSecretKeys:
      case aCheckKeys:
	if( opt.with_colons ) /* need this to list the trust */
	    rc = init_trustdb(1, trustdb_name );
	break;
      case aExportOwnerTrust: rc = init_trustdb( 0, trustdb_name ); break;
      case aListTrustDB: rc = init_trustdb( argc? 1:0, trustdb_name ); break;
      default: rc = init_trustdb(1, trustdb_name ); break;
    }
    if( rc )
	log_error(_("failed to initialize the TrustDB: %s\n"), g10_errstr(rc));


    switch( cmd ) {
      case aStore: /* only store the file */
	if( argc > 1 )
	    wrong_args(_("--store [filename]"));
	if( (rc = encode_store(fname)) )
	    log_error_f( print_fname_stdin(fname),
			"store failed: %s\n", g10_errstr(rc) );
	break;
    #ifdef IS_G10
      case aSym: /* encrypt the given file only with the symmetric cipher */
	if( argc > 1 )
	    wrong_args(_("--symmetric [filename]"));
	if( (rc = encode_symmetric(fname)) )
	    log_error_f(print_fname_stdin(fname),
			"symmetric encryption failed: %s\n",g10_errstr(rc) );
	break;

      case aEncr: /* encrypt the given file */
	if( argc > 1 )
	    wrong_args(_("--encrypt [filename]"));
	if( (rc = encode_crypt(fname,remusr)) )
	    log_error("%s: encryption failed: %s\n", print_fname_stdin(fname), g10_errstr(rc) );
	break;

      case aSign: /* sign the given file */
	sl = NULL;
	if( detached_sig ) { /* sign all files */
	    for( ; argc; argc--, argv++ )
		add_to_strlist( &sl, *argv );
	}
	else {
	    if( argc > 1 )
		wrong_args(_("--sign [filename]"));
	    if( argc ) {
		sl = m_alloc_clear( sizeof *sl + strlen(fname));
		strcpy(sl->d, fname);
	    }
	}
	if( (rc = sign_file( sl, detached_sig, locusr, 0, NULL, NULL)) )
	    log_error("signing failed: %s\n", g10_errstr(rc) );
	free_strlist(sl);
	break;

      case aSignEncr: /* sign and encrypt the given file */
	if( argc > 1 )
	    wrong_args(_("--sign --encrypt [filename]"));
	if( argc ) {
	    sl = m_alloc_clear( sizeof *sl + strlen(fname));
	    strcpy(sl->d, fname);
	}
	else
	    sl = NULL;
	if( (rc = sign_file(sl, detached_sig, locusr, 1, remusr, NULL)) )
	    log_error("%s: sign+encrypt failed: %s\n", print_fname_stdin(fname), g10_errstr(rc) );
	free_strlist(sl);
	break;

      case aClearsign: /* make a clearsig */
	if( argc > 1 )
	    wrong_args(_("--clearsign [filename]"));
	if( (rc = clearsign_file(fname, locusr, NULL)) )
	    log_error("%s: clearsign failed: %s\n", print_fname_stdin(fname), g10_errstr(rc) );
	break;

      case aVerify:
	if( (rc = verify_signatures( argc, argv ) ))
	    log_error("verify signatures failed: %s\n", g10_errstr(rc) );
	break;

      case aDecrypt:
	if( argc > 1 )
	    wrong_args(_("--decrypt [filename]"));
	if( (rc = decrypt_message( fname ) ))
	    log_error("decrypt_message failed: %s\n", g10_errstr(rc) );
	break;


      case aSignKey: /* sign the key given as argument */
      case aEditKey: /* Edit a key signature */
	if( argc != 1 )
	    wrong_args(_("--edit-key username"));
	keyedit_menu(fname, locusr );
	break;

      #endif /* IS_G10 */

      case aDeleteSecretKey:
	if( argc != 1 )
	    wrong_args(_("--delete-secret-key username"));
      case aDeleteKey:
	if( argc != 1 )
	    wrong_args(_("--delete-key username"));
	/* note: fname is the user id! */
	if( (rc = delete_key(fname, cmd==aDeleteSecretKey)) )
	    log_error("%s: delete key failed: %s\n", print_fname_stdin(fname), g10_errstr(rc) );
	break;


      case aCheckKeys:
	opt.check_sigs = 1;
      case aListSigs:
	opt.list_sigs = 1;
      case aListKeys:
	public_key_list( argc, argv );
	break;
      case aListSecretKeys:
	secret_key_list( argc, argv );
	break;

      case aKMode: /* list keyring */
	if( argc < 2 )	/* -kv [userid] */
	    public_key_list( (argc && **argv)? 1:0, argv );
	else if( argc == 2 ) { /* -kv userid keyring */
	    if( access( argv[1], R_OK ) ) {
		log_error(_("can't open %s: %s\n"),
			       print_fname_stdin(argv[1]), strerror(errno));
	    }
	    else {
		/* add keyring (default keyrings are not registered in this
		 * special case */
		add_keyring( argv[1] );
		public_key_list( **argv?1:0, argv );
	    }
	}
	else
	    wrong_args(_("-k[v][v][v][c] [userid] [keyring]") );
	break;

    #ifdef IS_G10
      case aKeygen: /* generate a key (interactive) */
	if( argc )
	    wrong_args("--gen-key");
	generate_keypair();
	break;
    #endif

      case aImport:
	if( !argc  ) {
	    rc = import_keys( NULL );
	    if( rc )
		log_error("import failed: %s\n", g10_errstr(rc) );
	}
	for( ; argc; argc--, argv++ ) {
	    rc = import_keys( *argv );
	    if( rc )
		log_error("import from '%s' failed: %s\n",
						*argv, g10_errstr(rc) );
	}
	break;

      case aExport:
	sl = NULL;
	for( ; argc; argc--, argv++ )
	    add_to_strlist( &sl, *argv );
	export_pubkeys( sl );
	free_strlist(sl);
	break;

      case aExportSecret:
	sl = NULL;
	for( ; argc; argc--, argv++ )
	    add_to_strlist( &sl, *argv );
	export_seckeys( sl );
	free_strlist(sl);
	break;

    #ifdef IS_G10
      case aGenRevoke:
	if( argc != 1 )
	    wrong_args("--gen-revoke user-id");
	gen_revoke( *argv );
	break;
    #endif

    #ifdef IS_G10MAINT
      case aDeArmor:
	if( argc > 1 )
	    wrong_args("--dearmor [file]");
	rc = dearmor_file( argc? *argv: NULL );
	if( rc )
	    log_error(_("dearmoring failed: %s\n"), g10_errstr(rc));
	break;

      case aEnArmor:
	if( argc > 1 )
	    wrong_args("--enarmor [file]");
	rc = enarmor_file( argc? *argv: NULL );
	if( rc )
	    log_error(_("enarmoring failed: %s\n"), g10_errstr(rc));
	break;


     #ifdef MAINTAINER_OPTIONS
      case aPrimegen:
	if( argc == 1 ) {
	    mpi_print( stdout, generate_public_prime( atoi(argv[0]) ), 1);
	    putchar('\n');
	}
	else if( argc == 2 ) {
	    mpi_print( stdout, generate_elg_prime( 0, atoi(argv[0]),
						   atoi(argv[1]), NULL,NULL ), 1);
	    putchar('\n');
	}
	else if( argc == 3 ) {
	    MPI g = mpi_alloc(1);
	    mpi_print( stdout, generate_elg_prime( 0, atoi(argv[0]),
						   atoi(argv[1]), g, NULL ), 1);
	    printf("\nGenerator: ");
	    mpi_print( stdout, g, 1 );
	    putchar('\n');
	    mpi_free(g);
	}
	else if( argc == 4 ) {
	    mpi_print( stdout, generate_elg_prime( 1, atoi(argv[0]),
						   atoi(argv[1]), NULL,NULL ), 1);
	    putchar('\n');
	}
	else
	    usage(1);
	break;
      #endif /* MAINTAINER OPTIONS */

      #ifdef MAINTAINER_OPTIONS
      case aGenRandom:
	if( argc < 1 || argc > 2 )
	    wrong_args("--gen-random level [hex]");
	{
	    int level = atoi(*argv);
	    for(;;) {
		byte *p = get_random_bits( 8, level, 0);
		if( argc == 1 ) {
		    printf("%02x", *p );
		    fflush(stdout);
		}
		else
		    putchar(c&0xff);
		m_free(p);
	    }
	}
	break;
      #endif /* MAINTAINER OPTIONS */

      case aPrintMD:
	if( argc < 1)
	    wrong_args("--print-md algo [file]");
	else {
	    int algo = string_to_digest_algo(*argv);

	    if( !algo )
		log_error(_("invalid hash algorithm '%s'\n"), *argv );
	    else {
		argc--; argv++;
		if( !argc )
		    print_mds(NULL, algo);
		else {
		    for(; argc; argc--, argv++ )
			print_mds(*argv, algo);
		}
	    }
	}
	break;

      case aPrintMDs:
	if( !argc )
	    print_mds(NULL,0);
	else {
	    for(; argc; argc--, argv++ )
		print_mds(*argv,0);
	}
	break;

     #ifdef MAINTAINER_OPTIONS
      case aTest: do_test( argc? atoi(*argv): 1 ); break;
      #endif /* MAINTAINER OPTIONS */

      case aListTrustDB:
	if( !argc )
	    list_trustdb(NULL);
	else {
	    for( ; argc; argc--, argv++ )
		list_trustdb( *argv );
	}
	break;

      case aCheckTrustDB:
	if( !argc )
	    check_trustdb(NULL);
	else {
	    for( ; argc; argc--, argv++ )
		check_trustdb( *argv );
	}
	break;

      case aListTrustPath:
	if( argc != 2 )
	    wrong_args("--list-trust-path [-- -]<maxdepth> <username>");
	list_trust_path( atoi(*argv), argv[1] );
	break;

      case aExportOwnerTrust:
	if( argc )
	    wrong_args("--export-ownertrust");
	export_ownertrust();
	break;

      case aImportOwnerTrust:
	if( argc > 1 )
	    wrong_args("--import-ownertrust [file]");
	import_ownertrust( argc? *argv:NULL );
	break;

     #endif /* IS_G10MAINT */


      case aListPackets:
	opt.list_packets=1;
      default:
	/* fixme: g10maint should do regular maintenace tasks here */
	if( argc > 1 )
	    wrong_args(_("[filename]"));
	if( !(a = iobuf_open(fname)) )
	    log_error(_("can't open '%s'\n"), print_fname_stdin(fname));
	else {
	    if( !opt.no_armor ) {
		if( use_armor_filter( a ) ) {
		    memset( &afx, 0, sizeof afx);
		    iobuf_push_filter( a, armor_filter, &afx );
		}
	    }
	    if( cmd == aListPackets ) {
		set_packet_list_mode(1);
		opt.list_packets=1;
	    }
	    proc_packets( a );
	    iobuf_close(a);
	}
	break;
    }

    /* cleanup */
    FREE_STRLIST(remusr);
    FREE_STRLIST(locusr);
    g10_exit(0);
    return 8; /*NEVER REACHED*/
}


void
g10_exit( int rc )
{
    if( opt.debug )
	secmem_dump_stats();
    secmem_term();
    rc = rc? rc : log_get_errorcount(0)? 2:0;
    /*write_status( STATUS_LEAVE );*/
    exit(rc );
}


void
do_not_use_RSA()
{
    static int did_rsa_note = 0;

    if( !did_rsa_note ) {
	did_rsa_note = 1;
	log_info(_("RSA keys are deprecated; please consider "
		   "creating a new key and use this key in the future\n"));
    }
}


#ifdef IS_G10MAINT
static void
print_hex( byte *p, size_t n )
{
    int i;

    if( n == 20 ) {
	for(i=0; i < n ; i++, i++, p += 2 ) {
	    if( i )
		putchar(' ');
	    if( i == 10 )
		putchar(' ');
	    printf("%02X%02X", *p, p[1] );
	}
    }
    else if( n == 24 ) {
	for(i=0; i < n ; i += 4, p += 4 ) {
	    if( i )
		putchar(' ');
	    if( i == 12 )
		putchar(' ');
	    printf("%02X%02X%02X%02X", *p, p[1], p[2], p[3] );
	}
    }
    else {
	for(i=0; i < n ; i++, p++ ) {
	    if( i )
		putchar(' ');
	    if( i && !(i%8) )
		putchar(' ');
	    printf("%02X", *p );
	}
    }
}

static void
print_mds( const char *fname, int algo )
{
    FILE *fp;
    char buf[1024];
    size_t n;
    MD_HANDLE md;
    char *pname;

    if( !fname ) {
	fp = stdin;
	pname = m_strdup("[stdin]: ");
    }
    else {
	pname = m_alloc(strlen(fname)+3);
	strcpy(stpcpy(pname,fname),": ");
	fp = fopen( fname, "rb" );
    }
    if( !fp ) {
	log_error("%s%s\n", pname, strerror(errno) );
	m_free(pname);
	return;
    }

    md = md_open( 0, 0 );
    if( algo )
	md_enable( md, algo );
    else {
	md_enable( md, DIGEST_ALGO_MD5 );
	md_enable( md, DIGEST_ALGO_SHA1 );
	md_enable( md, DIGEST_ALGO_RMD160 );
	if( !check_digest_algo(DIGEST_ALGO_TIGER) )
	    md_enable( md, DIGEST_ALGO_TIGER );
    }

    while( (n=fread( buf, 1, DIM(buf), fp )) )
	md_write( md, buf, n );
    if( ferror(fp) )
	log_error("%s%s\n", pname, strerror(errno) );
    else {
	md_final(md);
	if( algo ) {
	    if( fname )
		fputs( pname, stdout );
	    print_hex(md_read(md, algo), md_digest_length(algo) );
	}
	else {
	    printf(  "%s   MD5 = ", fname?pname:"" );
			    print_hex(md_read(md, DIGEST_ALGO_MD5), 16 );
	    printf("\n%s  SHA1 = ", fname?pname:""  );
			    print_hex(md_read(md, DIGEST_ALGO_SHA1), 20 );
	    printf("\n%sRMD160 = ", fname?pname:""  );
			    print_hex(md_read(md, DIGEST_ALGO_RMD160), 20 );
	    if( !check_digest_algo(DIGEST_ALGO_TIGER) ) {
		printf("\n%s TIGER = ", fname?pname:""  );
			    print_hex(md_read(md, DIGEST_ALGO_TIGER), 24 );
	    }
	}
	putchar('\n');
    }
    md_close(md);

    if( fp != stdin )
	fclose(fp);
}



#ifdef MAINTAINER_OPTIONS
static void
do_test(int times)
{
    m_check(NULL);
}
#endif /* MAINTAINER OPTIONS */
#endif /* IS_G10MAINT */

