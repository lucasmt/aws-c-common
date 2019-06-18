/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#undef memchr

#include <proof_helpers/nondet.h>
#include <stdlib.h>

void* memchr_impl(const void *str, int n, __CPROVER_size_t len) {
    (void)n;
    __CPROVER_precondition(__CPROVER_r_ok(str, len), "memchr string readable");
    size_t offset;
    __CPROVER_assume(offset < len);
    const char* rval = nondet_bool() ? str + offset : NULL;
    /*
    if(nondet_bool()) {
        __CPROVER_assume(rval >= str && rval < (str + len));
    } else {
        __CPROVER_assume(rval == NULL);
    }
    */
    return rval;
}

void *memchr(const void *str, int n, __CPROVER_size_t len) {
    return memchr_impl(str, n, len);
}
