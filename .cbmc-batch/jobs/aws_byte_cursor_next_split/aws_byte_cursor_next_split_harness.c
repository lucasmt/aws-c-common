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

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_byte_cursor_next_split_harness() {
    /* parameters */
    struct aws_byte_cursor input_str;
    struct aws_byte_cursor substr;
    char split_on;

    /* assumptions */
    ensure_byte_cursor_has_allocated_buffer_member(&input_str);
    __CPROVER_assume(aws_byte_cursor_is_valid(&input_str));
    __CPROVER_assume(__CPROVER_r_ok(input_str.ptr, input_str.len));
    if (nondet_bool()) {
        substr = input_str;
    } else if (nondet_bool()) {
	size_t offset;
	__CPROVER_assume(offset <= input_str.len);
	substr.ptr = input_str.ptr + offset;
	__CPROVER_assume(substr.len <= input_str.len - offset);
	__CPROVER_assume(aws_byte_cursor_is_valid(&substr));
    } else {
        substr.ptr = NULL;
	__CPROVER_assume(aws_byte_cursor_is_valid(&substr));
    }

    /* save current state of the data structure */
    /*
    struct aws_byte_cursor old_input_str = input_str;
    struct store_byte_from_buffer old_byte_from_input_str;
    save_byte_from_array(input_str.ptr, input_str.len, &old_byte_from_input_str);
    struct aws_byte_cursor old_substr = substr;
    struct store_byte_from_buffer old_byte_from_substr;
    save_byte_from_array(substr.ptr, substr.len, &old_byte_from_substr);
    */

    /* operation under verification */
    if (aws_byte_cursor_next_split(&input_str, split_on, &substr)) {
        /* TODO */
    }

    /* assertions */
    assert(aws_byte_cursor_is_valid(&input_str));
    assert(aws_byte_cursor_is_valid(&substr));
    //assert_byte_from_buffer_matches(lhs.ptr, &old_byte_from_lhs);
}
