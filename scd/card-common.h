/* card-common.h - Common declarations for all card types
 *	Copyright (C) 2001, 2002 Free Software Foundation, Inc.
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

#ifndef CARD_COMMON_H
#define CARD_COMMON_H


struct card_ctx_s {
  int reader;   /* used reader */
  struct sc_context *ctx;
  struct sc_card *scard;
  struct sc_pkcs15_card *p15card; /* only if there is a pkcs15 application */

  struct {
    int initialized;  /* the card has been initialied and the function
                         pointers may be used.  However for
                         unsupported operations the particular
                         function pointer is set to NULL */

    int (*enum_keypairs) (CARD card, int idx,
                          unsigned char *keygrip, char **keyid);
    int (*read_cert) (CARD card, const char *certidstr,
                      unsigned char **cert, size_t *ncert);
    int (*sign) (CARD card,
                 const char *keyidstr, int hashalgo,
                 int (pincb)(void*, const char *, char **),
                 void *pincb_arg,
                 const void *indata, size_t indatalen,
                 void **outdata, size_t *outdatalen );
    int (*decipher) (CARD card, const char *keyidstr,
                     int (pincb)(void*, const char *, char **),
                     void *pincb_arg,
                     const void *indata, size_t indatalen,
                     void **outdata, size_t *outdatalen);
  } fnc;
  
};

/*-- card.c --*/
int map_sc_err (int rc);
int card_help_get_keygrip (KsbaCert cert, unsigned char *array);



/* constructors */
void card_p15_bind (CARD card);
void card_dinsig_bind (CARD card);


#endif /*CARD_COMMON_H*/