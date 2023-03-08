#define A_NLIMBS 2
#define B_NLIMBS 2

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

/* Stucture of bignums
 * - limbs is an array representing the bignum by chunks of uint32_t in little endian representation
 * - nlimbs is the bound of the array
 **/
struct bignum_s {
	uint32_t *limbs;
	size_t nlimbs;
};
typedef struct bignum_s bignum_t;

bignum_t *bignum_add(bignum_t *a, bignum_t *b);
bignum_t *__bignum_add__(bignum_t *a, bignum_t *b);
uint32_t add_32_with_carry(uint32_t a, uint32_t b, uint32_t *carry);

void print_bignum(bignum_t *a);
void print_to_binary(uint32_t limb);

int main(void) {
	const size_t a_nlimbs = 1;
	uint32_t a_limbs[1] = {-1u}; // shortcut filling every element of the array with 1s 
	bignum_t bignum_a = {
		.limbs = a_limbs,
		.nlimbs = a_nlimbs
	};
	const size_t b_nlimbs = 2;
	uint32_t b_limbs[2] = {-1u, -1u}; // shortcut filling every element of the array with 1s 
	bignum_t bignum_b = {
		b_limbs,
		b_nlimbs
	};
	// add both bignums
	// print the result
	char u32_sp[] = "                                 ";
	printf("  %s%s", u32_sp, u32_sp);print_bignum(&bignum_a);
	printf("\n+ %s", u32_sp);print_bignum(&bignum_b);
	printf("\n= ");print_bignum(bignum_add(&bignum_a, &bignum_b));
	printf("\n");

	return EXIT_SUCCESS;
}

void print_to_binary(uint32_t limb) {
	for (size_t i = 0; i < 32; i++) {
		size_t bin_offset = 31-i;
		printf("%u", (limb & (1u << bin_offset)) >> bin_offset);
	}
}

void print_bignum(bignum_t *a) {
	for (size_t i = 0 ; i < a->nlimbs; i++) {
		size_t j = a->nlimbs - 1 - i; 
		print_to_binary(a->limbs[j]);
		printf(" ");
	}
}

uint32_t add_32_with_carry(uint32_t a, uint32_t b, uint32_t *carry) {
	uint32_t add = a + b;
	if (add < a || add < b) {
		*carry = 1u;
	} else {
		*carry = 0u;
	}
	return add;
}

/* Public function for adding two bignum_t
 * Actually a function ensuring the precondition of the actual sum function */
bignum_t *bignum_add(bignum_t *a, bignum_t *b) {
	// make sure a has the most limbs before calling the actual function
	if (a->nlimbs >= b->nlimbs) { 
		return __bignum_add__(a, b);
	}
	else {
		return __bignum_add__(b, a);
	}
}

/* Internal function, not advertized publicly
 * Precondition : a->nlimbs >= b->nlimbs */
bignum_t *__bignum_add__(bignum_t *a, bignum_t *b) {
	bignum_t *new_bignum = malloc(sizeof(bignum_t)); // bignum's struct allocation
	new_bignum->limbs = malloc((a->nlimbs + 1) * sizeof(uint32_t)); // reserve an additional limb in case of an overflow 
	uint32_t previous_loop_carry = 0u;
	size_t i; // index of iteration over the limbs
	for(i=0; i < b->nlimbs; i++) { // iteration over the first (common) limbs
		uint32_t first_carry; // a carry may occur when adding the previous loop carry to a's limb
		uint32_t a_limb_with_carry = add_32_with_carry(a->limbs[i], previous_loop_carry, &first_carry); // add a's limb to the previous loop carry
		uint32_t second_carry; // another carry may occur while subsequently adding b's limb
	       	new_bignum->limbs[i] = add_32_with_carry(a_limb_with_carry, b->limbs[i], &second_carry); // add b's limb to the result
		previous_loop_carry = first_carry | second_carry;
	}
	for (; i < a->nlimbs; i++) { // iteration over the remaining limbs only present in a, not in b 
		uint32_t first_carry; // a carry may still occur when adding the previous loop carry to a's limb
		new_bignum->limbs[i] = add_32_with_carry(a->limbs[i], previous_loop_carry, &first_carry); // add a's limb to the previous carry
		previous_loop_carry = first_carry;
	}
	if (previous_loop_carry == 1) { // in case a did overflow
	       	new_bignum->limbs[i] = 1u;
		new_bignum->nlimbs = a->nlimbs + 1; // the number of limbs needs to grow by 1 to accomodate the carry
	} else { // a did not overflow
		new_bignum->nlimbs = a->nlimbs; // the number of limbs stay the same as a
	}
	return new_bignum; 
}
