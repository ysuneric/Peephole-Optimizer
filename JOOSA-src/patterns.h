/*
 * JOOS is Copyright (C) 1997 Laurie Hendren & Michael I. Schwartzbach
 *
 * Reproduction of all or part of this software is permitted for
 * educational or research use on condition that this copyright notice is
 * included in any copy. This software comes with no warranty of any
 * kind. In no event will the authors be liable for any damages resulting from
 * use of this software.
 *
 * email: hendren@cs.mcgill.ca, mis@brics.dk
 */

/* iload x        iload x        iload x
 * ldc 0          ldc 1          ldc 2
 * imul           imul           imul
 * ------>        ------>        ------>
 * ldc 0          iload x        iload x
 *                               dup
 *                               iadd
 */

int simplify_multiplication_right(CODE **c) {
	int x, k;
	if (is_iload(*c, &x) &&
		is_ldc_int(next(*c), &k) &&
		is_imul(next(next(*c)))) {
		if (k == 0) return replace(c, 3, makeCODEldc_int(0, NULL));
		else if (k == 1) return replace(c, 3, makeCODEiload(x, NULL));
		else if (k == 2)
			return replace(c, 3, makeCODEiload(x,
											   makeCODEdup(
													   makeCODEiadd(NULL))));
		return 0;
	}
	return 0;
}

/* dup
 * astore x
 * pop
 * -------->
 * astore x
 */
int simplify_astore(CODE **c) {
	int x;
	if (is_dup(*c) &&
		is_astore(next(*c), &x) &&
		is_pop(next(next(*c)))) {
		return replace(c, 3, makeCODEastore(x, NULL));
	}
	return 0;
}

/* iload x
 * ldc k   (0<=k<=127)
 * iadd
 * istore x
 * --------->
 * iinc x k
 */
int positive_increment(CODE **c) {
	int x, y, k;
	if (is_iload(*c, &x) &&
		is_ldc_int(next(*c), &k) &&
		is_iadd(next(next(*c))) &&
		is_istore(next(next(next(*c))), &y) &&
		x == y && 0 <= k && k <= 127) {
		return replace(c, 4, makeCODEiinc(x, k, NULL));
	}
	return 0;
}

/* goto L1
 * ...
 * L1:
 * goto L2
 * ...
 * L2:
 * --------->
 * goto L2
 * ...
 * L1:    (reference count reduced by 1)
 * goto L2
 * ...
 * L2:    (reference count increased by 1)
 */
int simplify_goto_goto(CODE **c) {
	int l1, l2;
	if (is_goto(*c, &l1) && is_goto(next(destination(l1)), &l2) && l1 > l2) {
		droplabel(l1);
		copylabel(l2);
		return replace(c, 1, makeCODEgoto(l2, NULL));
	}
	return 0;
}

/****************** GROUP CODE BELOW *********************/

/*helper for collapse verification, reduce code duplication function*/
int collapse_satisfied(CODE **c, int label1) {
	int x, y, label2, label3;
	return (is_ldc_int(next(*c), &x) && x == 0 && is_goto(nextby(*c, 2), &label2) && uniquelabel(label2) &&
			is_label(nextby(*c, 3), &label3) && label3 == label1 && is_ldc_int(nextby(*c, 4), &y) && y == 1 &&
			is_label(nextby(*c, 5), &label3) && label3 == label2 && is_dup(nextby(*c, 6)) && is_pop(nextby(*c, 8)));
}

/*
 *
 */
int collapse_local_branching_with_dup(CODE **c) {
	int x, y, label, label1, label2, label3, label4, label5;

	/*ifeq initial branch*/
	if (is_ifeq(*c, &label1) && uniquelabel(label1)) {
		if (collapse_satisfied(c, label1)) {
			is_goto(nextby(*c, 2), &label);
			if (is_ifeq(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEifeq(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
																												NULL)))));
			} else if (is_ifne(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEifne(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
																												NULL)))));
			}
		}
	}
	/*ifne initial branch*/
	if (is_ifne(*c, &label1) && uniquelabel(label1)) {
		if (collapse_satisfied(c, label1)) {
			is_goto(nextby(*c, 2), &label);
			if (is_ifeq(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEifne(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
																												NULL)))));
			} else if (is_ifne(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEifeq(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
																												NULL)))));
			}
		}
	}

	/* ifnull initial branch */
	if (is_ifnull(*c, &label1) && uniquelabel(label1)) {
		if (collapse_satisfied(c, label1)) {
			is_goto(nextby(*c, 2), &label);
			if (is_ifeq(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEifnull(label1, makeCODEldc_int(0, makeCODEgoto(label2,
																							makeCODElabel(label1,
																										  NULL)))));
			} else if (is_ifne(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEifnonnull(label1, makeCODEldc_int(1, makeCODEgoto(label2,
																							   makeCODElabel(label1,
																											 NULL)))));
			}
		}
	}
	/*ifnonnull initial branch*/
	if (is_ifnull(*c, &label1) && uniquelabel(label1)) {
		if (collapse_satisfied(c, label1)) {
			is_goto(nextby(*c, 2), &label);
			if (is_ifeq(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEifnonnull(label1, makeCODEldc_int(0, makeCODEgoto(label2,
																							   makeCODElabel(label1,
																											 NULL)))));
			} else if (is_ifne(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEifnull(label1, makeCODEldc_int(1, makeCODEgoto(label2,
																							makeCODElabel(label1,
																										  NULL)))));
			}
		}
	}

	/*if acmpeq initial branch*/
	if (is_if_acmpeq(*c, &label1) && uniquelabel(label1)) {
		if (collapse_satisfied(c, label1)) {
			is_goto(nextby(*c, 2), &label);
			if (is_ifeq(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_acmpeq(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
																													 NULL)))));
			} else if (is_ifne(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_acmpne(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
																													 NULL)))));
			}
		}
	}
	/*if acmpne initial branch*/
	if (is_if_acmpne(*c, &label1) && uniquelabel(label1)) {
		if (collapse_satisfied(c, label1)) {
			is_goto(nextby(*c, 2), &label);
			if (is_ifeq(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_acmpne(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
																													 NULL)))));
			} else if (is_ifne(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_acmpeq(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
																													 NULL)))));
			}
		}
	}
	/*ificmpeq initial branch*/
	if (is_if_icmpeq(*c, &label1) && uniquelabel(label1)) {
		if (collapse_satisfied(c, label1)) {
			is_goto(nextby(*c, 2), &label);
			if (is_ifeq(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_icmpeq(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
																												NULL)))));
			} else if (is_ifne(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_icmpne(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
																												NULL)))));
			}
		}
	}
	/*ificmpne initial branch*/
	if (is_if_icmpne(*c, &label1) && uniquelabel(label1)) {
		if (collapse_satisfied(c, label1)) {
			is_goto(nextby(*c, 2), &label);
			if (is_ifeq(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_icmpne(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
																												NULL)))));
			} else if (is_ifne(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_icmpeq(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
																												NULL)))));
			}
		}
	}

	/*if icmpgt initial branch*/
	if (is_if_icmpgt(*c, &label1) && uniquelabel(label1)) {
		if (collapse_satisfied(c, label1)) {
			is_goto(nextby(*c, 2), &label);
			if (is_ifeq(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_icmpgt(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
																													 NULL)))));
			} else if (is_ifne(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_icmple(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
																													 NULL)))));
			}
		}
	}

	/*if icmplt initial branch*/
	if (is_if_icmplt(*c, &label1) && uniquelabel(label1)) {
		if (collapse_satisfied(c, label1)) {
			is_goto(nextby(*c, 2), &label);
			if (is_ifeq(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_icmplt(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
																													 NULL)))));
			} else if (is_ifne(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_icmpge(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
																													 NULL)))));
			}
		}
	}

	/*if icmpge initial branch*/
	if (is_if_icmpge(*c, &label1) && uniquelabel(label1)) {
		if (collapse_satisfied(c, label1)) {
			is_goto(nextby(*c, 2), &label);
			if (is_ifeq(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_icmpge(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
																													 NULL)))));
			} else if (is_ifne(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_icmplt(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
																													 NULL)))));
			}
		}
	}

	/*if icmple initial branch*/
	if (is_if_icmple(*c, &label1) && uniquelabel(label1)) {
		if (collapse_satisfied(c, label1)) {
			is_goto(nextby(*c, 2), &label);
			if (is_ifeq(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_icmple(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
																													 NULL)))));
			} else if (is_ifne(nextby(*c, 7), &label2)) {
				return replace(c, 9, makeCODEif_icmpgt(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
																													 NULL)))));
			}
		}
	}
	return 0;
}

/*
 * iconst 0     iconst 0
 * if icmpeq    if icmpne
 * ---->        --->
 * ifeq         ifne
 */
int simplify_cmpeq_cmpneq(CODE **c) {
	int x, y;
	if (is_ldc_int(*c, &x) && x == 0) {
		if (is_if_icmpeq(*c, &y)) {
			return replace(c, 2, makeCODEifeq(y, NULL));
		} else if (is_if_icmpne(*c, &y)) {
			return replace(c, 2, makeCODEifne(y, NULL));
		}
	}
	return 0;
}

/*
 * ireturn     areturn
 * goto        goto
 * ---->       ----->
 * ireturn     areturn
 */
int simplify_return_goto(CODE **c) {
	int x;
	if ((is_areturn(*c) || is_ireturn(*c)) && is_goto(next(*c), &x)) {
		droplabel(x);
		return replace(c, 2, makeCODEareturn(NULL));
	}
	return 0;
}

/*
 * aload     iload
 * astore    istore
 * ---->     ------>
 *
 */
int simplify_load_store(CODE **c) {
	int x, y;
	if (is_aload(*c, &x) && is_astore(next(*c), &y)) {
		if (x == y) return replace(c, 2, NULL);
	} else if (is_iload(*c, &x) && is_istore(next(*c), &y)) {
		if (x == y) return replace(c, 2, NULL);
	}
	return 0;
}

/*
 * swap
 * swap
 * ---->
 * swap
 */
int simplify_double_swap(CODE **c) {
	if (is_swap(*c) && is_swap(next(*c))) {
		return replace(c, 2, makeCODEswap(NULL));
	}
	return 0;
}

/*
 * dup
 * istore
 * pop
 * ----->
 * istore
 */
int simplify_istore(CODE **c) {
	int x;
	if (is_dup(*c) &&
		is_istore(next(*c), &x) &&
		is_pop(nextby(*c, 2))) {
		return replace(c, 3, makeCODEistore(x, NULL));
	}
	return 0;
}


/*  useless null replacements
 *  ifnull Label1 (unique?)
 *  goto Label2
 *  Label1:
 *  pop
 *  ldc "null" (string, may be an int)
 *  Label2
 *
 *  ----->
 *
 *  ifnonnull L2
 * pop
 * ldc x        (Integer or string)
 * L2:
 *
 *
 *
* ldc x
* dup
* ifnull L
* --------->
* ldc x
*/

int simplify_null_check(CODE **c){
    int x,y,a,b;
    int z;
    char *str;
    if(
        is_ifnull(*c, &x) && uniquelabel(x) &&
        is_goto(next(*c), &y) &&
        is_label(next(next(*c)), &a) &&
        is_pop(next(next(next(*c)))) &&
        is_ldc_string(next(next(next(next(*c)))),&str) &&
        is_label(next(next(next(next(next(*c))))), &b)){
        if(y == b && x == a) return replace(c, 5, makeCODEifnonnull(y,makeCODEpop(makeCODEldc_string(str, makeCODElabel(y,NULL)))));
    }
    if(
            is_ifnull(*c, &x) && uniquelabel(x) &&
            is_goto(next(*c), &y) &&
            is_label(next(next(*c)), &a) &&
            is_pop(next(next(next(*c)))) &&
            is_ldc_int(next(next(next(next(*c)))),&z) &&
            is_label(next(next(next(next(next(*c))))), &b)){
        if(y == b && x == a) return replace(c, 5, makeCODEifnonnull(y,makeCODEpop(makeCODEldc_int(z, makeCODElabel(y,NULL)))));
    }
    if(is_ldc_int(*c, &x) &&
        is_dup(next(*c)) &&
        is_ifnull(next(next(*c)), &a)){
        return replace(c, 3, makeCODEldc_int(x, NULL));
    }
    if(is_ldc_string(*c, &str) &&
       is_dup(next(*c)) &&
       is_ifnull(next(next(*c)), &a)){
        return replace(c, 3, makeCODEldc_string(str, NULL));
    }
    return 0;
}


int simplify_useless_comparison(CODE **c){
    int x,y,a,a1,b,b1,d;
    int check = 0;
    if(is_if_icmpeq(*c, &a)){
        check = 1;
    } else if(is_if_icmpne(*c, &a)){
        check = 2;
    } else if(is_if_icmplt(*c, &a)){
        check = 3;
    } else if(is_if_icmple(*c, &a)){
        check = 4;
    } else if(is_if_icmpgt(*c, &a)){
        check = 5;
    } else if(is_if_icmpge(*c, &a)){
        check = 6;
    } else if(is_ifeq(*c, &a)){
        check = 7;
    } else if(is_ifne(*c, &a)){
        check = 8;
    }

    if(check != 0 &&
        is_ldc_int(next(*c), &x) &&
        is_goto(next(next(*c)),&b) &&
        is_label(next(next(next(*c))),&a1) &&
        is_ldc_int(next(next(next(next(*c)))), &y) &&
        is_label(next(next(next(next(next(*c))))),&b1) &&
        is_ifeq(next(next(next(next(next(next(*c)))))), &d) &&
        (x == 0 && y == 1 && a == a1 && b == b1) &&
        uniquelabel(a) && uniquelabel(b)){
        switch (check){
            case 1: return(replace(c, 7,makeCODEif_icmpne(d,NULL)));
            case 2: return(replace(c, 7,makeCODEif_icmpeq(d,NULL)));
            case 3: return(replace(c, 7,makeCODEif_icmpge(d,NULL)));
            case 4: return(replace(c, 7,makeCODEif_icmpgt(d,NULL)));
            case 5: return(replace(c, 7,makeCODEif_icmple(d,NULL)));
            case 6: return(replace(c, 7,makeCODEif_icmplt(d,NULL)));
            case 7: return(replace(c, 7,makeCODEifne(d,NULL)));
            case 8: return(replace(c, 7,makeCODEifeq(d,NULL)));
            default: return 0;
        }

    }
    return 0;
}


/*
 * Conversion extra nop line 793?
 *  ireturn
 *  nop
 *  ------>
 *  ireturn
 *
 *  OR
 *
 *  return
 *  nop
 *  ----->
 *  return
 */

int remove_extra_nop(CODE **c)
{ if ((is_ireturn(*c) || is_return(*c)) && is_nop(next(*c))) {
        if(is_return(*c)) return replace(c, 2, makeCODEreturn(NULL));
        else if(is_ireturn(*c)) return replace(c, 2, makeCODEireturn(NULL));
    }

    return 0;
}


/*
 *  return
 *  goto start_4
 *
 *  ------>
 *
 *  areturn
 */

int remove_extra_goto(CODE **c) {
	int x;
	if (is_areturn(*c) &&
		is_goto(next(*c), &x)) {
		return replace_modified(c, 2, makeCODEareturn(NULL));
	}
	if (is_ireturn(*c) &&
		is_goto(next(*c), &x)) {
		return replace_modified(c, 2, makeCODEireturn(NULL));
	}
	return 0;
}


/*
 *  replace decrements with single line
 *  iload x
 *  ldc k   (0>=k>=-127)
 *  iadd
 *  istore x
 *  --------->
 *  iinc x k
 */

int negative_increment(CODE **c) {
	int x, y, k;
	if (is_iload(*c, &x) &&
		is_ldc_int(next(*c), &k) &&
		is_iadd(next(next(*c))) &&
		is_istore(next(next(next(*c))), &y)) {
		if (x == y && k <= 0 && -127 <= k)return replace(c, 4, makeCODEiinc(x, k, NULL));
	}
	return 0;
}

/* iload x
 * ldc k   (0<=k<=128)
 * isub
 * istore x
 * --------->
 * iinc x k
 */
int positive_decrement(CODE **c)
{ int x,y,k;
    if (is_iload(*c,&x) &&
        is_ldc_int(next(*c),&k) &&
        is_isub(next(next(*c))) &&
        is_istore(next(next(next(*c))),&y) &&
        x==y && 0<=k && k<=128) {
        return replace(c,4,makeCODEiinc(x,-k,NULL));
    }
    return 0;
}

/* iload x
 * ldc k   (-128<=k<=0)
 * isub
 * istore x
 * --------->
 * iinc x k
 */
int negative_decrement(CODE **c) {
	int x, y, k;
	if (is_iload(*c, &x) &&
		is_ldc_int(next(*c), &k) &&
		is_isub(next(next(*c))) &&
		is_istore(next(next(next(*c))), &y) &&
		x == y && 0 >= k && k >= -128) {
		return replace(c, 4, makeCODEiinc(x, k, NULL));
	}
	return 0;
}

/* better memory from dup
 * aload i
 * aload i
 *
 * ----->
 *
 * aload i
 * dup
 *
 */

int double_aload(CODE **c) {
	int x, y;
	if (is_aload(*c, &x) &&
		is_aload(next(*c), &y)) {
		if (x == y) return replace(c, 2, makeCODEaload(x, makeCODEdup(NULL)));
	}
	return 0;
}

/* better memory from dup
 * aload i
 * aload i
 *
 * ----->
 *
 * aload i
 * dup
 *
 */

int double_iload(CODE **c) {
	int x, y;
	if (is_iload(*c, &x) &&
		is_iload(next(*c), &y)) {
		if (x == y) return replace(c, 2, makeCODEiload(x, makeCODEdup(NULL)));
	}
	return 0;
}

/*
 * istore i
 * istore i
 *
 * ---->
 *
 * istore i
 */

int double_istore(CODE **c) {
	int x, y;
	if (is_istore(*c, &x) &&
		is_istore(next(*c), &y)) {
		if (x == y)return replace(c, 2, makeCODEistore(x, NULL));
	}
	return 0;
}

/*
 * astore i
 * astore i
 *
 * ---->
 *
 * astore i
 */

int double_astore(CODE **c) {
	int x, y;
	if (is_astore(*c, &x) &&
		is_astore(next(*c), &y)) {
		if (x == y)return replace(c, 2, makeCODEastore(x, NULL));
	}
	return 0;
}

/*
 * istore i
 * iload i
 *
 * ---->
 *
 * dup
 * istore i
 */
int i_store_load(CODE **c) {
	int x, y;
	if (is_istore(*c, &x) &&
		is_iload(next(*c), &y)) {
		if (x == y) return replace(c, 2, makeCODEdup(makeCODEistore(x, NULL)));
	}
	return 0;
}

/*
* istore i
* iload i
*
* ---->
*
* dup
* istore i
*/
int a_store_load(CODE **c) {
	int x, y;
	if (is_astore(*c, &x) &&
		is_aload(next(*c), &y)) {
		if (x == y)return replace(c, 2, makeCODEdup(makeCODEastore(x, NULL)));
	}
	return 0;
}

/*
 * load i
 * store i
 *
 * ---->
 *
 * nothing
 */
int load_store(CODE **c) {
	int x, y, a, b;
	if (is_aload(*c, &x) &&
		is_astore(next(*c), &y)) {
		if (x == y)return replace(c, 2, NULL);
	} else if (is_iload(*c, &a) &&
			   is_istore(next(*c), &b)) {
		if (a == b) return replace(c, 2, NULL);
	}
	return 0;
}

/* iload x        iload x
 * ldc 0          ldc 0
 * iadd           isub
 * ------>        ------>
 * iload x        iload x
 *
 * ldc x        ildc x
 * ldc 0          ldc 0
 * iadd           isub
 * ------>        ------>
 * iload x        iload x
 *
 *
 */

int simplify_add_sub_right(CODE **c) {
	int x, k;
	if (is_iload(*c, &x) &&
		is_ldc_int(next(*c), &k) &&
		(is_iadd(next(next(*c))) || is_isub(next(next(*c))))) {
		if (k == 0) return replace(c, 3, makeCODEiload(x, NULL));

        return 0;
    }
    if (is_ldc_int(*c,&x) &&
        is_ldc_int(next(*c),&k) &&
        (is_iadd(next(next(*c))) || is_isub(next(next(*c))))) {
        if (k==0) return replace(c,3,makeCODEldc_int(x, NULL));

        return 0;
    }
    return 0;
}

/* ldc 0        ldc 0
 * iload x          iload x
 * iadd           isub
 * ------>        ------>
 * iload x        iload x
 *
 * ldc 0          ldc 0
 * ldc x          ldc x
 * iadd           isub
 * ------>        ------>
 * iload x        iload x
 *
 *
 */

int simplify_add_sub_left(CODE **c)
{ int x,k;
    if (is_ldc_int(*c,&x) &&
        is_iload(next(*c),&k) &&
        (is_iadd(next(next(*c))) || is_isub(next(next(*c))))) {
        if (k==0) return replace(c,3,makeCODEiload(x, NULL));

        return 0;
    }
    if (is_ldc_int(*c,&k) &&
        is_ldc_int(next(*c),&x) &&
        (is_iadd(next(next(*c))) || is_isub(next(next(*c))))) {
        if (k==0) return replace(c,3,makeCODEldc_int(x, NULL));

        return 0;
    }
    return 0;
}

/* iload x
 * ldc 1
 * idiv
 * ------>
 * iload x
 *
 * ldc x
 * ldc 1
 * idiv
 * ------>
 * ldc x
 *
 */

int simplify_division_right(CODE **c)
{ int x,k;
    if (is_iload(*c,&x) &&
        is_ldc_int(next(*c),&k) &&
        is_idiv(next(next(*c)))) {
        if (k==1) return replace(c,3,makeCODEiload(x,NULL));
    }
    if (is_ldc_int(*c,&x) &&
        is_ldc_int(next(*c),&k) &&
        is_idiv(next(next(*c)))) {
        if (k==1) return replace(c,3,makeCODEldc_int(x,NULL));
    }

    return 0;
}

/* ldc 0          ldc 0          ldc 2
 * iload x        iload x        iload x
 * imul           imul           imul
 * ------>        ------>        ------>
 * ldc 0          iload x        iload x
 *                               dup
 *                               iadd
 */

int simplify_multiplication_left(CODE **c) {
	int x, k;
	if (is_ldc_int(*c, &k) &&
		is_iload(next(*c), &x) &&
		is_imul(next(next(*c)))) {
		if (k == 0) return replace(c, 3, makeCODEldc_int(0, NULL));
		else if (k == 1) return replace(c, 3, makeCODEiload(x, NULL));
		else if (k == 2)
			return replace(c, 3, makeCODEiload(x,
											   makeCODEdup(
													   makeCODEiadd(NULL))));
		return 0;
	}
	return 0;
}


/*
 * consider strings
 *  ldc a / load a
 *  ldc b / load b
 *  swap
 *
 *  ---->
 *
 *  ldc b / load b
 *  ldc a / load a
 */

int load_load_swap(CODE **c) {
	int x, y, a, b, i, j;
	char *str1, *str2;
	if (is_ldc_int(*c, &x) &&
		is_ldc_int(next(*c), &y) &&
		is_swap(next(next(*c)))) {
		if (x == y) {
			return replace(c, 3, makeCODEldc_int(x, makeCODEdup(NULL)));
		} else {
			return replace(c, 3, makeCODEldc_int(y, makeCODEldc_int(x, NULL)));
		}
	}
	if (is_iload(*c, &a) &&
		is_iload(next(*c), &b) &&
		is_swap(next(next(*c)))) {
		if (a == b) {
			return replace(c, 3, makeCODEiload(a, makeCODEdup(NULL)));
		} else {
			return replace(c, 3, makeCODEiload(b, makeCODEiload(a, NULL)));
		}
	}
	if (is_aload(*c, &i) &&
		is_aload(next(*c), &j) &&
		is_swap(next(next(*c)))) {
		if (i == j) {
			return replace(c, 3, makeCODEaload(i, makeCODEdup(NULL)));
		} else {
			return replace(c, 3, makeCODEaload(j, makeCODEaload(i, NULL)));
		}
	}
	if (is_ldc_string(*c, &str1) &&
		is_ldc_string(next(*c), &str2) &&
		is_swap(next(next(*c)))) {
		if (strcmp(str1, str2) == 0) {
			return replace(c, 3, makeCODEldc_string(str1, makeCODEdup(NULL)));
		} else {
			return replace(c, 3, makeCODEldc_string(str2, makeCODEldc_string(str1, NULL)));
		}
	}
	return 0;
}


/*
 * dup
 * aload 0
 * swap
 * putfield
 * pop
 * --------->
 * aload 0
 * swap
 * putfield
 */
int simplify_putfield(CODE **c) {
	int x;
	char *y;
	if (is_dup(*c) &&
		is_aload(next(*c), &x) &&
		is_swap(next(next(*c))) &&
		is_putfield(next(next(next(*c))), &y) &&
		is_pop(next(next(next(next(*c)))))) {
		if (x == 0) return replace(c, 5, makeCODEaload(x, makeCODEswap(makeCODEputfield(y, NULL))));
	}
	return 0;
}


void init_patterns(void) {
	ADD_PATTERN(simplify_multiplication_right);
	ADD_PATTERN(simplify_astore);
	ADD_PATTERN(positive_increment);
	ADD_PATTERN(simplify_goto_goto);


	/*ben adds*/
    ADD_PATTERN(double_aload);
    ADD_PATTERN(double_iload);
	ADD_PATTERN(double_astore);
    ADD_PATTERN(double_istore);
    ADD_PATTERN(a_store_load);
    ADD_PATTERN(i_store_load);
    ADD_PATTERN(load_store);
    ADD_PATTERN(load_load_swap);
    ADD_PATTERN(negative_increment);
    ADD_PATTERN(positive_decrement);
    ADD_PATTERN(negative_decrement);
    ADD_PATTERN(simplify_null_check);
    ADD_PATTERN(simplify_add_sub_right);
    ADD_PATTERN(simplify_add_sub_left);
    ADD_PATTERN(simplify_division_right);
    ADD_PATTERN(simplify_multiplication_left);
    ADD_PATTERN(remove_extra_goto);
    ADD_PATTERN(simplify_putfield);
    ADD_PATTERN(remove_extra_nop);
    ADD_PATTERN(simplify_useless_comparison);


	ADD_PATTERN(simplify_istore);
	ADD_PATTERN(simplify_double_swap);
	ADD_PATTERN(simplify_load_store);
	ADD_PATTERN(simplify_return_goto);
	ADD_PATTERN(simplify_cmpeq_cmpneq);
	ADD_PATTERN(collapse_local_branching_with_dup);
}
