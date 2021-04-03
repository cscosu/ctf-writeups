/* WARNING: Could not reconcile some variable overlaps */
/* compute(std::map<int, std::vector<int, std::allocator<int>>, std::less<int>,
   std::allocator<std::pair<int const, std::vector<int, std::allocator<int>>>>>) */

undefined8 compute(map param_1)

{
  char cmp_res;
  bool bVar1;
  long *q_front;
  int *curr_mapval_vec_val_ptr;
  long set_size;
  long map_size;
  undefined8 ret;
  undefined4 in_register_0000003c;
    
  map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
  *this;
  long in_FS_OFFSET;
  int curr_key;
  int curr_mapval_vec_val;
  int local_d8;
  int curr_val;
  undefined8 curr_mapval_vec_iter;
  undefined8 firstkey_findcurr_mapvalend;
  vector<int,std::allocator<int>> *curr_mapval_vec;
  undefined8 firstval_currpair;
  undefined8 firstpair_end_nextpair;
  set<int,std::less<int>,std::allocator<int>> setboi [48];
  queue<std::pair<int,int>,std::deque<std::pair<int,int>,std::allocator<std::pair<int,int>>>>
  queueboi [88];
  long local_20;
  
  this = (
          map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
          *)CONCAT44(in_register_0000003c,param_1);
  local_20 = *(long *)(in_FS_OFFSET + 0x28);
  std::set<int,std::less<int>,std::allocator<int>>::set(setboi);
                    /* try { // try from 001023d1 to 001023d5 has its CatchHandler @ 00102668 */
  std::queue<std::pair<int,int>,std::deque<std::pair<int,int>,std::allocator<std::pair<int,int>>>>::
  queue<std::deque<std::pair<int,int>,std::allocator<std::pair<int,int>>>,void>(queueboi);
  firstval_currpair = (ulong)firstval_currpair._4_4_ << 0x20;
  firstkey_findcurr_mapvalend = CONCAT44(firstkey_findcurr_mapvalend._4_4_,4);
  std::pair<int,int>::pair<int,int,true>
            ((pair<int,int> *)&firstpair_end_nextpair,(int *)&firstkey_findcurr_mapvalend,
             (int *)&firstval_currpair);
                    /* try { // try from 0010241b to 001025c6 has its CatchHandler @ 00102657 */
  std::queue<std::pair<int,int>,std::deque<std::pair<int,int>,std::allocator<std::pair<int,int>>>>::
  emplace<std::pair<int,int>>(queueboi,(pair *)&firstpair_end_nextpair);
  do {
    do {
      cmp_res = std::
                queue<std::pair<int,int>,std::deque<std::pair<int,int>,std::allocator<std::pair<int,int>>>>
                ::empty(queueboi);
      if (cmp_res == '\x01') {
        set_size = std::set<int,std::less<int>,std::allocator<int>>::size(setboi);
        map_size = std::
                   map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
                   ::size(this);
        if ((set_size == map_size) &&
           (set_size = std::
                       map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
                       ::size(this), set_size == 6
                    /* function returns when true is empty - true if set and map are both size 6 */)
           ) {
          ret = 1;
        }
        else {
          ret = 0;
        }
end_compute:
        std::
        queue<std::pair<int,int>,std::deque<std::pair<int,int>,std::allocator<std::pair<int,int>>>>
        ::~queue(queueboi);
        std::set<int,std::less<int>,std::allocator<int>>::~set(setboi);
        if (local_20 == *(long *)(in_FS_OFFSET + 0x28)) {
          return ret;
        }
                    /* WARNING: Subroutine does not return */
        __stack_chk_fail();
      }
      q_front = (long *)std::
                        queue<std::pair<int,int>,std::deque<std::pair<int,int>,std::allocator<std::pair<int,int>>>>
                        ::front();
      firstval_currpair = *q_front;
      std::
      queue<std::pair<int,int>,std::deque<std::pair<int,int>,std::allocator<std::pair<int,int>>>>::
      pop(queueboi);
      curr_key = (int)firstval_currpair;
      curr_val = firstval_currpair._4_4_;
      firstpair_end_nextpair = std::set<int,std::less<int>,std::allocator<int>>::end(setboi);
      firstkey_findcurr_mapvalend =
           std::set<int,std::less<int>,std::allocator<int>>::find(setboi,&curr_key);
      cmp_res = std::operator!=((_Rb_tree_const_iterator *)&firstkey_findcurr_mapvalend,
                                (_Rb_tree_const_iterator *)&firstpair_end_nextpair);
    } while (cmp_res != '\0');
    std::set<int,std::less<int>,std::allocator<int>>::emplace<int&>(setboi,&curr_key);
    if (curr_val + 4 != curr_key) {
      ret = 0;
      goto end_compute;
    }
    curr_mapval_vec =
         (vector<int,std::allocator<int>> *)
         std::
         map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
         ::operator[](this,&curr_key);
    curr_mapval_vec_iter = std::vector<int,std::allocator<int>>::begin(curr_mapval_vec);
    firstkey_findcurr_mapvalend = std::vector<int,std::allocator<int>>::end(curr_mapval_vec);
    while (bVar1 = __gnu_cxx::operator!=
                             ((__normal_iterator *)&curr_mapval_vec_iter,
                              (__normal_iterator *)&firstkey_findcurr_mapvalend), bVar1 != false) {
      curr_mapval_vec_val_ptr =
           (int *)__gnu_cxx::__normal_iterator<int*,std::vector<int,std::allocator<int>>>::operator*
                            ((__normal_iterator<int*,std::vector<int,std::allocator<int>>> *)
                             &curr_mapval_vec_iter);
      curr_mapval_vec_val = *curr_mapval_vec_val_ptr;
      local_d8 = curr_val + 1;
      std::pair<int,int>::pair<int&,int,true>
                ((pair<int,int> *)&firstpair_end_nextpair,&curr_mapval_vec_val,&local_d8);
      std::
      queue<std::pair<int,int>,std::deque<std::pair<int,int>,std::allocator<std::pair<int,int>>>>::
      emplace<std::pair<int,int>>(queueboi,(pair *)&firstpair_end_nextpair);
      __gnu_cxx::__normal_iterator<int*,std::vector<int,std::allocator<int>>>::operator++
                ((__normal_iterator<int*,std::vector<int,std::allocator<int>>> *)
                 &curr_mapval_vec_iter);
    }
  } while( true );
}

