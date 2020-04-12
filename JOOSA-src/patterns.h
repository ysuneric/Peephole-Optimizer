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

int simplify_multiplication_right(CODE **c)
{ int x,k;
  if (is_iload(*c,&x) &&
      is_ldc_int(next(*c),&k) &&
      is_imul(next(next(*c)))) {
     if (k==0) return replace(c,3,makeCODEldc_int(0,NULL));
     else if (k==1) return replace(c,3,makeCODEiload(x,NULL));
     else if (k==2) return replace(c,3,makeCODEiload(x,
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
int simplify_astore(CODE **c)
{ int x;
  if (is_dup(*c) &&
      is_astore(next(*c),&x) &&
      is_pop(next(next(*c)))) {
     return replace(c,3,makeCODEastore(x,NULL));
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
int positive_increment(CODE **c)
{ int x,y,k;
  if (is_iload(*c,&x) &&
      is_ldc_int(next(*c),&k) &&
      is_iadd(next(next(*c))) &&
      is_istore(next(next(next(*c))),&y) &&
      x==y && 0<=k && k<=127) {
     return replace(c,4,makeCODEiinc(x,k,NULL));
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
int simplify_goto_goto(CODE **c)
{ int l1,l2;
  if (is_goto(*c,&l1) && is_goto(next(destination(l1)),&l2) && l1>l2) {
     droplabel(l1);
     copylabel(l2);
     return replace(c,1,makeCODEgoto(l2,NULL));
  }
  return 0;
}

/****************** GROUP CODE BELOW *********************/


/*
 * dup
 * istore
 * pop
 * ----->
 * istore
 */
int simplify_istore(CODE **c)
{ int x;
	if (is_dup(*c) &&
		is_istore(next(*c),&x) &&
		is_pop(nextby(*c,2))) {
		return replace(c,3,makeCODEistore(x,NULL));
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
    if( //string
        is_ifnull(*c, &x) && uniquelabel(x) &&
        is_goto(next(*c), &y) &&
        is_label(next(next(*c)), &a) &&
        is_pop(next(next(next(*c)))) &&
        is_ldc_string(next(next(next(next(*c)))),&str) &&
        is_label(next(next(next(next(next(*c))))), &b)){
        if(y == b && x == a) return replace(c, 5, makeCODEifnonnull(y,makeCODEpop(makeCODEldc_string(str, makeCODElabel(y,NULL)))));
    }
    if( //int
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
        is_ifnull(next(next(*c)), &a)){ //int
        return replace(c, 3, makeCODEldc_int(x, NULL));
    }
    if(is_ldc_string(*c, &str) &&
       is_dup(next(*c)) &&
       is_ifnull(next(next(*c)), &a)){ //string
        return replace(c, 3, makeCODEldc_string(str, NULL));
    }
    return 0;
}

/*
 *  useless comparision\
 *  if_icmpeq true_21
 *  iconst_0
 *  goto stop_22
 *  true_21:
 *  iconst_1
 *  stop_22:
 *  ifeq else_19
 *
 *
 *  ------>
 *
 *  if_icmp true_21:
 *  goto else19
 *  true_21:
 *
 */
int simplify_if_else(CODE **c){
    int x,y,z,a,b;
    if(is_if_icmpeq(*c, &x) &&
        is_goto(next(next(*c)),&y) &&
            is_label(next(next(next(*c))),&z) &&
            is_label(next(next(next(next(next(*c))))),&a) &&
            is_ifeq(next(next(next(next(next(next(*c)))))), &b)){
       return replace(c, 7, makeCODEif_icmpeq(x,
                makeCODEgoto(b,
                        makeCODElabel(x,NULL))));
    }
    return 0;
}

/*
 * Conversion extra nop line 793?
 *  i2c
 *  ireturn
 *  nop
 *  .end method
 */


/*
 *  return
 *  goto start_4
 *
 *  ------>
 *
 *  areturn
 */

int remove_extra_goto(CODE **c)
{   int x;
    if (is_areturn(*c) &&
        is_goto(next(*c),&x)) {
        return replace_modified(c, 2, makeCODEareturn(NULL));
    }
    if (is_ireturn(*c) &&
        is_goto(next(*c),&x)) {
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

int negative_increment(CODE **c)
{ int x,y,k;
    if (is_iload(*c,&x) &&
        is_ldc_int(next(*c),&k) &&
        is_iadd(next(next(*c))) &&
        is_istore(next(next(next(*c))),&y)) {
        if(x==y && k<=0 && -127<=k)return replace(c,4,makeCODEiinc(x,k,NULL));
    }
    return 0;
}

/* iload x
 * ldc k   (0<=k<=127)
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
        x==y && 0<=k && k<=127) {
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
int negative_decrement(CODE **c)
{ int x,y,k;
    if (is_iload(*c,&x) &&
        is_ldc_int(next(*c),&k) &&
        is_isub(next(next(*c))) &&
        is_istore(next(next(next(*c))),&y) &&
        x==y && 0>=k && k>=-128) {
        return replace(c,4,makeCODEiinc(x,k,NULL));
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

int double_aload(CODE **c)
{ int x,y;
    if (is_aload(*c,&x) &&
        is_aload(next(*c),&y)) {
        if(x==y) return replace(c,2, makeCODEaload(x, makeCODEdup(NULL)));
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

int double_iload(CODE **c)
{ int x,y;
    if (is_iload(*c,&x) &&
        is_iload(next(*c),&y)) {
        if(x==y) return replace(c,2, makeCODEiload(x, makeCODEdup(NULL)));
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

int double_istore(CODE **c)
{ int x,y;
    if (is_istore(*c,&x) &&
        is_istore(next(*c),&y)) {
        if(x==y)return replace(c,2, makeCODEistore(x, NULL));
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

int double_astore(CODE **c)
{ int x,y;
    if (is_astore(*c,&x) &&
        is_astore(next(*c),&y)) {
        if(x==y)return replace(c,2, makeCODEastore(x, NULL));
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
int i_store_load(CODE **c)
{ int x,y;
    if (is_istore(*c,&x) &&
        is_iload(next(*c),&y)) {
        if(x==y) return replace(c,2, makeCODEdup(makeCODEistore(x,NULL)));
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
int a_store_load(CODE **c)
{ int x,y;
    if (is_astore(*c,&x) &&
        is_aload(next(*c),&y)){
        if(x==y)return replace(c,2, makeCODEdup(makeCODEastore(x, NULL)));
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
int load_store(CODE **c)
{ int x,y,a,b;
    if (is_aload(*c,&x) &&
        is_astore(next(*c),&y)) {
        if(x==y)return replace(c,2, NULL);
    }  else if(is_iload(*c,&a) &&
                 is_istore(next(*c),&b)) {
        if(a == b) return replace(c,2, NULL);
    }
    return 0;
}

/* iload x        iload x
 * ldc 0          ldc 0
 * iadd           isub
 * ------>        ------>
 * iload x        iload x
 *
 *
 */

int simplify_add_sub_right(CODE **c)
{ int x,k;
    if (is_iload(*c,&x) &&
        is_ldc_int(next(*c),&k) &&
            (is_iadd(next(next(*c))) || is_isub(next(next(*c))))) {
        if (k==0) return replace(c,3,makeCODEiload(x, NULL));

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
 *
 */

int simplify_division_right(CODE **c)
{ int x,k;
    if (is_iload(*c,&x) &&
        is_ldc_int(next(*c),&k) &&
        is_idiv(next(next(*c)))) {
        if (k==1) return replace(c,3,makeCODEiload(x,NULL));

        return 0;
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

int simplify_multiplication_left(CODE **c)
{ int x,k;
    if (is_ldc_int(*c,&k) &&
        is_iload(next(*c),&x) &&
        is_imul(next(next(*c)))) {
        if (k==0) return replace(c,3,makeCODEldc_int(0,NULL));
        else if (k==1) return replace(c,3,makeCODEiload(x,NULL));
        else if (k==2) return replace(c,3,makeCODEiload(x,
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

int load_load_swap(CODE **c)
{ int x,y,a,b,i,j;
    char *str1, *str2;
    if (is_ldc_int(*c,&x) &&
         is_ldc_int(next(*c),&y)  &&
         is_swap(next(next(*c)))){
        if(x == y){
            return replace(c,3, makeCODEldc_int(x, makeCODEdup(NULL)));
        } else {
            return replace(c,3, makeCODEldc_int(y, makeCODEldc_int(x, NULL)));
        }
    }
    if (is_iload(*c,&a) &&
                is_iload(next(*c),&b)  &&
                is_swap(next(next(*c)))){
        if(a == b){
            return replace(c,3, makeCODEiload(a, makeCODEdup(NULL)));
        } else {
            return replace(c,3, makeCODEiload(b, makeCODEiload(a, NULL)));
        }
    }
    if(is_aload(*c,&i) &&
                is_aload(next(*c),&j)  &&
                is_swap(next(next(*c)))) {
        if(i == j){
            return replace(c,3, makeCODEaload(i, makeCODEdup(NULL)));
        } else {
            return replace(c,3, makeCODEaload(j, makeCODEaload(i, NULL)));
        }
    }
    if (is_ldc_string(*c,&str1) &&
        is_ldc_string(next(*c),&str2)  &&
        is_swap(next(next(*c)))){
        if(strcmp(str1, str2) == 0){
            return replace(c,3, makeCODEldc_string(str1, makeCODEdup(NULL)));
        } else {
            return replace(c,3, makeCODEldc_string(str2, makeCODEldc_string(str1, NULL)));
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
int simplify_putfield(CODE **c)
{   int x;
    char* y;
    if (is_dup(*c) &&
        is_aload(next(*c), &x) &&
        is_swap(next(next(*c))) &&
        is_putfield(next(next(next(*c))), &y) &&
        is_pop(next(next(next(next(*c)))))) {
        if(x == 0) return replace(c, 5, makeCODEaload(x, makeCODEswap( makeCODEputfield(y, NULL))));
    }
    return 0;
}







void init_patterns(void) {
	ADD_PATTERN(simplify_multiplication_right);
	ADD_PATTERN(simplify_astore);
	ADD_PATTERN(positive_increment);
	ADD_PATTERN(simplify_goto_goto);


	/*ben adds*/
    ADD_PATTERN(simplify_if_else);
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
    ADD_PATTERN(simplify_division_right);
    ADD_PATTERN(simplify_multiplication_left);
    ADD_PATTERN(remove_extra_goto);
    ADD_PATTERN(simplify_putfield);

	ADD_PATTERN(simplify_istore);
    /*
 *
 *
 * */


}
