/**
 *  Copyright (C) 2011
 *  University of Rochester Department of Computer Science
 *    and
 *  Lehigh University Department of Computer Science and Engineering
 *
 * License: Modified BSD
 *          Please see the file LICENSE.RSTM for licensing information
 */

#ifndef RSTM_FOREACH_HPP
#define RSTM_FOREACH_HPP

/**
 * C++ iterators can get so ugly without c++0x 'auto'.  These macros are not
 * a good idea, but it makes it much easier to write 79-column code
 */
#define FOREACH(TYPE, VAR, COLLECTION)                  \
    for (TYPE::iterator VAR = COLLECTION.begin(),       \
         CEND = COLLECTION.end();                       \
         VAR != CEND; ++VAR)

#endif // RSTM_FOREACH_HPP
