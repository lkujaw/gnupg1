/* app-common.h - Common declarations for all card applications
 *	Copyright (C) 2003 Free Software Foundation, Inc.
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

#ifndef GNUPG_SCD_APP_COMMON_H
#define GNUPG_SCD_APP_COMMON_H

#if GNUPG_MAJOR_VERSION != 1
#include <ksba.h>
#endif

struct app_local_s;  /* Defined by all app-*.c.  */

struct app_ctx_s {
  int initialized;  /* The application has been initialied and the
                       function pointers may be used.  Note that for
                       unsupported operations the particular
                       function pointer is set to NULL */
  int slot;         /* Used reader. */
  unsigned char *serialno; /* Serialnumber in raw form, allocated. */
  size_t serialnolen;      /* Length in octets of serialnumber. */
  const char *apptype;
  unsigned int card_version;
  int did_chv1;
  int force_chv1;   /* True if the card does not cache CHV1. */
  int did_chv2;
  int did_chv3;
  struct app_local_s *app_local;  /* Local to the application. */
  struct {
    void (*deinit) (app_t app);
    int (*learn_status) (app_t app, ctrl_t ctrl);
    int (*readcert) (app_t app, const char *certid,
                     unsigned char **cert, size_t *certlen);
    int (*getattr) (app_t app, ctrl_t ctrl, const char *name);
    int (*setattr) (app_t app, const char *name,
                    int (*pincb)(void*, const char *, char **),
                    void *pincb_arg,
                    const unsigned char *value, size_t valuelen);
    int (*sign) (app_t app,
                 const char *keyidstr, int hashalgo,
                 int (pincb)(void*, const char *, char **),
                 void *pincb_arg,
                 const void *indata, size_t indatalen,
                 unsigned char **outdata, size_t *outdatalen );
    int (*auth) (app_t app, const char *keyidstr,
                 int (*pincb)(void*, const char *, char **),
                 void *pincb_arg,
                 const void *indata, size_t indatalen,
                 unsigned char **outdata, size_t *outdatalen);
    int (*decipher) (app_t app, const char *keyidstr,
                     int (pincb)(void*, const char *, char **),
                     void *pincb_arg,
                     const void *indata, size_t indatalen,
                     unsigned char **outdata, size_t *outdatalen);
    int (*genkey) (app_t app, ctrl_t ctrl,
                   const char *keynostr, unsigned int flags,
                   int (*pincb)(void*, const char *, char **),
                   void *pincb_arg);
    int (*change_pin) (app_t app, ctrl_t ctrl,
                       const char *chvnostr, int reset_mode,
                       int (*pincb)(void*, const char *, char **),
                       void *pincb_arg);
    int (*check_pin) (app_t app, const char *keyidstr,
                      int (pincb)(void*, const char *, char **),
                      void *pincb_arg);
  } fnc;

};

#if GNUPG_MAJOR_VERSION == 1
int app_select_openpgp (app_t app);
int app_get_serial_and_stamp (app_t app, char **serial, time_t *stamp);
#else
/*-- app-help.c --*/
gpg_error_t app_help_get_keygrip_string (ksba_cert_t cert, char *hexkeygrip);
size_t app_help_read_length_of_cert (int slot, int fid, size_t *r_certoff);


/*-- app.c --*/
app_t select_application (ctrl_t ctrl, int slot, const char *name);
void release_application (app_t app);
int app_get_serial_and_stamp (app_t app, char **serial, time_t *stamp);
int app_write_learn_status (app_t app, ctrl_t ctrl);
int app_readcert (app_t app, const char *certid,
                  unsigned char **cert, size_t *certlen);
int app_getattr (app_t app, ctrl_t ctrl, const char *name);
int app_setattr (app_t app, const char *name,
                 int (*pincb)(void*, const char *, char **),
                 void *pincb_arg,
                 const unsigned char *value, size_t valuelen);
int app_sign (app_t app, const char *keyidstr, int hashalgo,
              int (pincb)(void*, const char *, char **),
              void *pincb_arg,
              const void *indata, size_t indatalen,
              unsigned char **outdata, size_t *outdatalen );
int app_auth (app_t app, const char *keyidstr,
              int (*pincb)(void*, const char *, char **),
              void *pincb_arg,
              const void *indata, size_t indatalen,
              unsigned char **outdata, size_t *outdatalen);
int app_decipher (app_t app, const char *keyidstr,
                  int (pincb)(void*, const char *, char **),
                  void *pincb_arg,
                  const void *indata, size_t indatalen,
                  unsigned char **outdata, size_t *outdatalen );
int app_genkey (app_t app, ctrl_t ctrl,
                const char *keynostr, unsigned int flags,
                int (*pincb)(void*, const char *, char **),
                void *pincb_arg);
int app_get_challenge (app_t app, size_t nbytes, unsigned char *buffer);
int app_change_pin (app_t app, ctrl_t ctrl,
                    const char *chvnostr, int reset_mode,
                    int (*pincb)(void*, const char *, char **),
                    void *pincb_arg);
int app_check_pin (app_t app, const char *keyidstr,
                   int (*pincb)(void*, const char *, char **),
                   void *pincb_arg);


/*-- app-openpgp.c --*/
int app_select_openpgp (app_t app);

int app_openpgp_cardinfo (app_t app,
                          char **serialno,
                          char **disp_name,
                          char **pubkey_url,
                          unsigned char **fpr1,
                          unsigned char **fpr2,
                          unsigned char **fpr3);
#endif /* GNUPG_MAJOR_VERSION != 1 */
int app_openpgp_storekey (app_t app, int keyno,
                          unsigned char *template, size_t template_len,
                          time_t created_at,
                          const unsigned char *m, size_t mlen,
                          const unsigned char *e, size_t elen,
                          int (*pincb)(void*, const char *, char **),
                          void *pincb_arg);
int app_openpgp_readkey (app_t app, int keyno,
                         unsigned char **m, size_t *mlen,
                         unsigned char **e, size_t *elen);
#if GNUPG_MAJOR_VERSION == 1
#else
/*-- app-nks.c --*/
int app_select_nks (app_t app);

/*-- app-dinsig.c --*/
int app_select_dinsig (app_t app);


#endif /* GNUPG_MAJOR_VERSION != 1 */


#endif /*GNUPG_SCD_APP_COMMON_H*/



