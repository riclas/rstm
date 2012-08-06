/**
 *  Copyright (C) 2011
 *  University of Rochester Department of Computer Science
 *    and
 *  Lehigh University Department of Computer Science and Engineering
 *
 * License: Modified BSD
 *          Please see the file LICENSE.RSTM for licensing information
 */

/**
 * OrecLazyHB is the name for the oreclazy algorithm when instantiated with
 * HourglassBackoffCM.  Virtually all of the code is in the oreclazy.hpp
 * file, but we need to instantiate in order to use the "HourglassBackoffCM"
 * object, which employs both backoff and the "Hourglass" (from the "Toxic
 * Transactions" paper).
 */

#include "OrecLazy.hpp"
#include "cm.hpp"
#include "adaptivity.hpp"
#include "tm_alloc.hpp"


/**
 * Instantiate rollback with the appropriate CM for this TM algorithm. This
 * works because the templated functions in OrecLazy have the right names.
 */
INSTANTIATE_FOR_CM(HourglassBackoffCM, 18)

/**
 *  For querying to get the current algorithm name
 */
const char* alg_tm_getalgname() {
    return "OrecLazyHB";
}

/**
 *  Register the TM for adaptivity and for use as a standalone library
 */
REGISTER_TM_FOR_ADAPTIVITY(OrecLazyHB)

