#include <stdint.h>



struct bignum_s {
	uint32_t *limbs;
	size_t nlimbs;
};

typedef bignum_s bignum_t;

void bignum_add_inplace(bignum_t *a, bignum_t *b);

bignum_t *bignum_add(bignum_t *a, bignum_t *b);

int main(int argc, char** argv) {

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

bignum_t *bignum_add(bignum_t *a, bignum_t *b) {
	bignum_t *new_bignum = malloc(sizeof(bignum_t)); //allocation de la structure bignum
	if (a->nlimbs > b->nlimbs) {
		new_bignum->nlimbs = a->nlimbs;
	}
	else {
		new_bignum->nlimbs = b->nlimbs;
	}
	new_bignum->limbs = malloc(new_bignum->nlimbs * sizeof(uint32_t));
	uint32_t carry = 0u;
	for(size_t i=0; i < a->nlimbs; i++) {
		uint32_t previous_carry = carry;
		uint32_t c = add_32_with_carry(a->limbs[i], previous_carry, &carry);
		uint32_t new_carry;
	       	new_bignum->limbs[i] = add_32_with_carry(c, b->limbs[i], &new_carry);
		carry = new_carry | carry;
	}
}
