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

/*
 * new
 * dup
 * ldc
 * invoke
 * aload
 * swap
 * ------>
 * aload
 * new
 * dup
 * ldc
 * invoke
 *
 * soundness: arguments are the same, no stack difference
 */
int simplify_swap_invoke(CODE **c) {
	char *arg1, *arg2;
	int x, y;
	if (is_new(*c, &arg1) && is_dup(next(*c)) && is_ldc_int(nextby(*c, 2), &x) &&
		is_invokenonvirtual(nextby(*c, 3), &arg2) && is_aload(nextby(*c, 4), &y) && is_swap(nextby(*c, 5))) {
		return replace(c, 6, makeCODEaload(y, makeCODEnew(arg1, makeCODEdup(
				makeCODEldc_int(x, makeCODEinvokenonvirtual(arg2, NULL))))));
	}
	return 0;
}

/*helper for collapse verification, reduce code duplication function*/
int collapse_satisfied(CODE **c, int label1) {
	int x, y, label2, label3;
	return (is_ldc_int(next(*c), &x) && x == 0 && is_goto(nextby(*c, 2), &label2) && uniquelabel(label2) &&
			is_label(nextby(*c, 3), &label3) && label3 == label1 && is_ldc_int(nextby(*c, 4), &y) && y == 1 &&
			is_label(nextby(*c, 5), &label3) && label3 == label2 && is_dup(nextby(*c, 6)) && is_pop(nextby(*c, 8)));
}

/*
 * control_flow Label1     	control_flow Label1
 * iconst 0					iconst 0
 * goto Label2				goto Label2
 * Label1					Label1
 * iconst 1					iconst 1
 * Label2					Label2
 * dup						dup
 * ifeq Label3				ifne Label3
 * pop						pop
 * ---->					------>
 * control_flow Label1		opposite_control_flow label1
 * load 0					load 1
 * goto Label3				goto Label3
 * Label1					Label1
 *
 * The control flow logic is the same, if control flow is true or false we load a 1 or 0 respectively. duplicaate that value
 * and then check for eq/ne. in the optimized expression, we first jump if the control flow is not satisfied, then load
 * 1/0 depending on the original ifne vs ifeq. strictly smaller instrution set and stack is unchanged.
 */
int collapse_usless_comparison_with_dup(CODE **c) {
	int label, label1, label2;

    int check = 0;
    if(is_ifeq(*c, &label1)){
        check = 1;
    } else if(is_ifne(*c, &label1)){
        check = 2;
    } else if(is_ifnull(*c, &label1)){
        check = 3;
    } else if(is_ifnonnull(*c, &label1)){
        check = 4;
    } else if(is_if_acmpeq(*c, &label1)){
        check = 5;
    } else if(is_if_acmpne(*c, &label1)){
        check = 6;
    } else if(is_if_icmpeq(*c, &label1)){
        check = 7;
    } else if(is_if_icmpne(*c, &label1)) {
        check = 8;
    } else if(is_if_icmpgt(*c, &label1)){
        check = 9;
    } else if(is_if_icmplt(*c, &label1)){
        check = 10;
    } else if(is_if_icmpge(*c, &label1)){
        check = 11;
    } else if(is_if_icmple(*c, &label1)){
        check = 12;
    }

    if(check != 0 && collapse_satisfied(c, label1) && uniquelabel(label1)){
        is_goto(nextby(*c, 2), &label);
        switch(check){
            case 1: /*ifeq initial branch*/
                if (is_ifeq(nextby(*c, 7), &label2)) {
                    return replace(c, 9, makeCODEifeq(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                    NULL)))));
                } else if (is_ifne(nextby(*c, 7), &label2)) {
                    return replace(c, 9, makeCODEifne(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                    NULL)))));
                }
                break;
            case 2: /*ifne initial branch*/
                if (is_ifeq(nextby(*c, 7), &label2)) {
                    return replace(c, 9, makeCODEifne(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                    NULL)))));
                } else if (is_ifne(nextby(*c, 7), &label2)) {
                    return replace(c, 9, makeCODEifeq(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                    NULL)))));
                }
                break;
            case 3: /* ifnull initial branch */
                if (is_ifeq(nextby(*c, 7), &label2)) {
                    return replace(c, 9, makeCODEifnull(label1, makeCODEldc_int(0, makeCODEgoto(label2,
                                                                                                makeCODElabel(label1,
                                                                                                              NULL)))));
                } else if (is_ifne(nextby(*c, 7), &label2)) {
                    return replace(c, 9, makeCODEifnonnull(label1, makeCODEldc_int(1, makeCODEgoto(label2,
                                                                                                   makeCODElabel(label1,
                                                                                                                 NULL)))));
                }
                break;
            case 4: /*ifnonnull initial branch*/
                if (is_ifeq(nextby(*c, 7), &label2)) {
                    return replace(c, 9, makeCODEifnonnull(label1, makeCODEldc_int(0, makeCODEgoto(label2,
                                                                                                   makeCODElabel(label1,
                                                                                                                 NULL)))));
                } else if (is_ifne(nextby(*c, 7), &label2)) {
                    return replace(c, 9, makeCODEifnull(label1, makeCODEldc_int(1, makeCODEgoto(label2,
                                                                                                makeCODElabel(label1,
                                                                                                              NULL)))));
                }
                break;
            case 5: /*if acmpeq initial branch*/
                if (is_ifeq(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_acmpeq(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                } else if (is_ifne(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_acmpne(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                }
                break;
            case 6: /*if acmpne initial branch*/
                if (is_ifeq(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_acmpne(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                } else if (is_ifne(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_acmpeq(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                }
                break;
            case 7: /*ificmpeq initial branch*/
                if (is_ifeq(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_icmpeq(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                } else if (is_ifne(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_icmpne(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                }
                break;
            case 8: /*ificmpne initial branch*/
                if (is_ifeq(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_icmpne(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                } else if (is_ifne(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_icmpeq(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                }
                break;
            case 9: /*if icmpgt initial branch*/
                if (is_ifeq(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_icmpgt(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                } else if (is_ifne(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_icmple(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                }
                break;
            case 10: /*if icmplt initial branch*/
                if (is_ifeq(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_icmplt(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                } else if (is_ifne(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_icmpge(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                }
                break;
            case 11: /*if icmpge initial branch*/
                if (is_ifeq(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_icmpge(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                } else if (is_ifne(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_icmplt(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                }
                break;
            case 12: /*if icmple initial branch*/
                if (is_ifeq(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_icmple(label1, makeCODEldc_int(0, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                } else if (is_ifne(nextby(*c, 7), &label2)) {
                    return replace(c, 9,
                                   makeCODEif_icmpgt(label1, makeCODEldc_int(1, makeCODEgoto(label2, makeCODElabel(label1,
                                                                                                                   NULL)))));
                }
                break;

        }
    }

	return 0;
}

/*
 * iconst 0     iconst 0
 * if icmpeq    if icmpne
 * ---->        --->
 * ifeq         ifne
 *
 * soundness:
 * [...:x]
 * [...: x: 0]
 * [...]
 * ------> works since ifeq/ifne compare to zero already
 * [...:x]
 * [...]
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
 * aload     iload
 * astore    istore
 * ---->     ------>
 *
 * soundness: no change to overall computation.
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
 *
 * soundness: swap + swap = no change on stack
 */
int simplify_double_swap(CODE **c) {
	if (is_swap(*c) && is_swap(next(*c))) {
		return replace(c, 2, NULL);
	}
	return 0;
}

/*
 * dup
 * istore
 * pop
 * ----->
 * istore
 *
 * soundness:
 * [...: x]
 * [... : x : x] dup
 * [... : x ] store
 * [...] pop
 * ---->
 * [...: x]
 * [...] istore
 *
 * start and end stack same, strictly decreasing, no hcange in computation.
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

 * ldc x
 * dup
 * ifnull L
 * --------->
 * ldc x
 */

int simplify_null_check(CODE **c) {
	int x, y, a, b;
	int z;
	char *str;
	if (
			is_ifnull(*c, &x) && uniquelabel(x) &&
			is_goto(next(*c), &y) &&
			is_label(next(next(*c)), &a) &&
			is_pop(next(next(next(*c)))) &&
			is_ldc_string(next(next(next(next(*c)))), &str) &&
			is_label(next(next(next(next(next(*c))))), &b)) {
		if (y == b && x == a) return replace(c, 5, makeCODEifnonnull(y, makeCODEpop(
					makeCODEldc_string(str, makeCODElabel(y, NULL)))));
	}
	if (
			is_ifnull(*c, &x) && uniquelabel(x) &&
			is_goto(next(*c), &y) &&
			is_label(next(next(*c)), &a) &&
			is_pop(next(next(next(*c)))) &&
			is_ldc_int(next(next(next(next(*c)))), &z) &&
			is_label(next(next(next(next(next(*c))))), &b)) {
		if (y == b && x == a) return replace(c, 5, makeCODEifnonnull(y, makeCODEpop(
					makeCODEldc_int(z, makeCODElabel(y, NULL)))));
	}
	if (is_ldc_int(*c, &x) &&
		is_dup(next(*c)) &&
		is_ifnull(next(next(*c)), &a)) {
		return replace(c, 3, makeCODEldc_int(x, NULL));
	}
	if (is_ldc_string(*c, &str) &&
		is_dup(next(*c)) &&
		is_ifnull(next(next(*c)), &a)) {
		return replace(c, 3, makeCODEldc_string(str, NULL));
	}
	return 0;
}

/*
 * if_icmpeq a || if_icmpne a || if_icmplt a || if_icmple a || if_icmpgt a || if_icmpge a || if_eg a || if_ne a
 * ldc x (x = 0)
 * goto b
 * a1:
 * ldc y (y = 1)
 * b1:
 * ifeq d
 * ----->
 * if_icmpne a || if_icmpeq a || if_icmpge a || if_icmpgt a || if_icmple a || if_icmplt a || if_ne a || if_eg a
 *
 *
 */
int simplify_useless_comparison(CODE **c) {
	int x, y, a, a1, b, b1, d;
	int check = 0;
	if (is_if_icmpeq(*c, &a)) {
		check = 1;
	} else if (is_if_icmpne(*c, &a)) {
		check = 2;
	} else if (is_if_icmplt(*c, &a)) {
		check = 3;
	} else if (is_if_icmple(*c, &a)) {
		check = 4;
	} else if (is_if_icmpgt(*c, &a)) {
		check = 5;
	} else if (is_if_icmpge(*c, &a)) {
		check = 6;
	} else if (is_ifeq(*c, &a)) {
		check = 7;
	} else if (is_ifne(*c, &a)) {
		check = 8;
	}

	if (check != 0 &&
		is_ldc_int(next(*c), &x) &&
		is_goto(next(next(*c)), &b) &&
		is_label(next(next(next(*c))), &a1) &&
		is_ldc_int(next(next(next(next(*c)))), &y) &&
		is_label(next(next(next(next(next(*c))))), &b1) &&
		is_ifeq(next(next(next(next(next(next(*c)))))), &d) &&
		(x == 0 && y == 1 && a == a1 && b == b1) &&
		uniquelabel(a) && uniquelabel(b)) {
		switch (check) {
			case 1:
				return (replace(c, 7, makeCODEif_icmpne(d, NULL)));
			case 2:
				return (replace(c, 7, makeCODEif_icmpeq(d, NULL)));
			case 3:
				return (replace(c, 7, makeCODEif_icmpge(d, NULL)));
			case 4:
				return (replace(c, 7, makeCODEif_icmpgt(d, NULL)));
			case 5:
				return (replace(c, 7, makeCODEif_icmple(d, NULL)));
			case 6:
				return (replace(c, 7, makeCODEif_icmplt(d, NULL)));
			case 7:
				return (replace(c, 7, makeCODEifne(d, NULL)));
			case 8:
				return (replace(c, 7, makeCODEifeq(d, NULL)));
			default:
				return 0;
		}
	}
	return 0;
}

/*
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
 *
 *  soundness: noop after return is never hit.
 */
int remove_extra_nop(CODE **c) {
	if ((is_ireturn(*c) || is_return(*c)) && is_nop(next(*c))) {
		if (is_return(*c)) return replace(c, 2, makeCODEreturn(NULL));
		else if (is_ireturn(*c)) return replace(c, 2, makeCODEireturn(NULL));
	}

	return 0;
}

/*
 *   *  a/ireturn
 *  goto start_4
 *
 *  ------>
 *
 *  a/ireturn
 *
 *  soundness: goto never reached, strictly decreasing
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
 *
 *  soundness: strictly decreasing, and no stack changes. all increment and decrement have same reasoning
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
 * soundness: strictly decreasing, and no stack changes. all increment and decrement have same reasoning
 */
int positive_decrement(CODE **c) {
	int x, y, k;
	if (is_iload(*c, &x) &&
		is_ldc_int(next(*c), &k) &&
		is_isub(next(next(*c))) &&
		is_istore(next(next(next(*c))), &y) &&
		x == y && 0 <= k && k <= 128) {
		return replace(c, 4, makeCODEiinc(x, -k, NULL));
	}
	return 0;
}

/* iload x
 * ldc k   (-128<=k<=0)
 * isub
 * istore x
 * --------->
 * iinc x k
 * soundness: strictly decreasing, and no stack changes. all increment and decrement have same reasoning
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
 * soundness, no change to stack, strictly less bits
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
 * soundness: no change to stack ,strictly less bits
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
 *
 * storing same value twice is useless, strictly less arguments
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
 * same as istore soundenss, useless extra operation
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
 *
 * strictly less bits, no change to stack
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
 *
 * same as i store load, no change to stack strictly less bits
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
 *
 * load store does nothing in terms of computation, stricly smaller stack,
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
 * simplifying mathematical invariants
 */
int simplify_add_sub_right(CODE **c) {
	int x, k;
	if (is_iload(*c, &x) &&
		is_ldc_int(next(*c), &k) &&
		(is_iadd(next(next(*c))) || is_isub(next(next(*c))))) {
		if (k == 0) return replace(c, 3, makeCODEiload(x, NULL));

		return 0;
	}
	if (is_ldc_int(*c, &x) &&
		is_ldc_int(next(*c), &k) &&
		(is_iadd(next(next(*c))) || is_isub(next(next(*c))))) {
		if (k == 0) return replace(c, 3, makeCODEldc_int(x, NULL));

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
 * more mathematical invariants
 */
int simplify_add_sub_left(CODE **c) {
	int x, k;
	if (is_ldc_int(*c, &x) &&
		is_iload(next(*c), &k) &&
		(is_iadd(next(next(*c))) || is_isub(next(next(*c))))) {
		if (k == 0) return replace(c, 3, makeCODEiload(x, NULL));

		return 0;
	}
	if (is_ldc_int(*c, &k) &&
		is_ldc_int(next(*c), &x) &&
		(is_iadd(next(next(*c))) || is_isub(next(next(*c))))) {
		if (k == 0) return replace(c, 3, makeCODEldc_int(x, NULL));

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
 * more invariants
 */
int simplify_division_right(CODE **c) {
	int x, k;
	if (is_iload(*c, &x) &&
		is_ldc_int(next(*c), &k) &&
		is_idiv(next(next(*c)))) {
		if (k == 1) return replace(c, 3, makeCODEiload(x, NULL));
	}
	if (is_ldc_int(*c, &x) &&
		is_ldc_int(next(*c), &k) &&
		is_idiv(next(next(*c)))) {
		if (k == 1) return replace(c, 3, makeCODEldc_int(x, NULL));
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
 * more invariants
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
 *
 *  simplify swap, stack unchanged, fewer instructions
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
 *
 * simplify superfluous dup pop, instructions are the same, stack unchanged
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
	ADD_PATTERN(simplify_cmpeq_cmpneq);
	ADD_PATTERN(collapse_usless_comparison_with_dup);
	ADD_PATTERN(simplify_swap_invoke);
}
