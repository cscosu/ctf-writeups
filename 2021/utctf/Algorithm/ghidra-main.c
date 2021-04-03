/* WARNING: Could not reconcile some variable overlaps */

undefined8 main(void)

{
  int iVar1;
  char cVar2;
  bool bVar3;
  long *plVar4;
  basic_ostream *pbVar5;
  basic_istream<char,std::char_traits<char>> *this;
  vector<int,std::allocator<int>> *pvVar6;
  pair *ppVar7;
  int *piVar8;
  size_t n;
  uchar *d;
  long in_FS_OFFSET;
  int num_pairs;
  int pair_ctr;
  int flag_pos;
  int local_44c;
  undefined8 num_key;
  undefined8 num_val;
  undefined8 key_iter;
  undefined8 val_iter;
  map *local_428;
  undefined8 *local_420;
  map pair_map [12];
  undefined8 end_iter;
  undefined8 local_3e0;
  undefined8 local_3d8;
  basic_string inp [32];
  basic_string<char,std::char_traits<char>,std::allocator<char>> local_398 [32];
  __cxx11 local_378 [32];
  basic_string local_358 [400];
  undefined4 local_1c8 [4];
  undefined4 local_1b8;
  undefined4 local_1b4;
  undefined4 local_1b0;
  undefined4 local_1ac;
  undefined4 local_1a8;
  undefined4 local_1a4;
  undefined4 local_1a0;
  undefined4 local_19c;
  undefined4 local_198;
  undefined4 local_194;
  undefined4 local_190;
  undefined4 local_18c;
  undefined4 local_188;
  undefined4 local_184;
  byte digest_out [24];
  long local_20;
  
  local_20 = *(long *)(in_FS_OFFSET + 0x28);
  std::operator<<((basic_ostream *)std::cout,"Input a number:\n");
  std::__cxx11::basic_string<char,std::char_traits<char>,std::allocator<char>>::basic_string();
                    /* try { // try from 001026de to 0010270c has its CatchHandler @ 00102fb8 */
  std::getline<char,std::char_traits<char>,std::allocator<char>>((basic_istream *)std::cin,inp);
  std::operator|(0x10,8);
  iVar1 = (int)register0x00000020;
  std::__cxx11::basic_stringstream<char,std::char_traits<char>,std::allocator<char>>::
  basic_stringstream(local_358,iVar1 - 0x3b8);
                    /* try { // try from 00102721 to 00102751 has its CatchHandler @ 00102fa4 */
  plVar4 = (long *)std::basic_istream<char,std::char_traits<char>>::operator>>
                             ((basic_istream<char,std::char_traits<char>> *)local_358,&num_pairs);
  cVar2 = std::basic_ios<char,std::char_traits<char>>::operator!
                    ((basic_ios<char,std::char_traits<char>> *)
                     ((long)plVar4 + *(long *)(*plVar4 + -0x18)));
  if (cVar2 != '\0') {
    std::operator<<((basic_ostream *)std::cout,"That\'s not a number\n");
                    /* WARNING: Subroutine does not return */
    exit(1);
  }
  std::
  map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
  ::map((
         map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
         *)pair_map);
                    /* try { // try from 00102779 to 001027fb has its CatchHandler @ 00102f90 */
  pbVar5 = std::operator<<((basic_ostream *)std::cout,"Input ");
  pbVar5 = (basic_ostream *)
           std::basic_ostream<char,std::char_traits<char>>::operator<<
                     ((basic_ostream<char,std::char_traits<char>> *)pbVar5,num_pairs);
  std::operator<<(pbVar5," pairs of numbers:\n");
  pair_ctr = 0;
  while (pair_ctr < num_pairs) {
    std::getline<char,std::char_traits<char>,std::allocator<char>>((basic_istream *)std::cin,inp);
    std::operator|(0x10,8);
    std::__cxx11::basic_stringstream<char,std::char_traits<char>,std::allocator<char>>::
    basic_stringstream((basic_string *)local_1c8,iVar1 - 0x3b8);
                    /* try { // try from 00102810 to 00102814 has its CatchHandler @ 00102ea8 */
    std::__cxx11::basic_stringstream<char,std::char_traits<char>,std::allocator<char>>::operator=
              ((basic_stringstream<char,std::char_traits<char>,std::allocator<char>> *)local_358,
               (basic_stringstream *)local_1c8);
    std::__cxx11::basic_stringstream<char,std::char_traits<char>,std::allocator<char>>::
    ~basic_stringstream((basic_stringstream<char,std::char_traits<char>,std::allocator<char>> *)
                        local_1c8);
                    /* try { // try from 00102838 to 001028b6 has its CatchHandler @ 00102f90 */
    this = (basic_istream<char,std::char_traits<char>> *)
           std::basic_istream<char,std::char_traits<char>>::operator>>
                     ((basic_istream<char,std::char_traits<char>> *)local_358,(int *)&num_key);
    plVar4 = (long *)std::basic_istream<char,std::char_traits<char>>::operator>>
                               (this,(int *)&num_val);
    cVar2 = std::basic_ios<char,std::char_traits<char>>::operator!
                      ((basic_ios<char,std::char_traits<char>> *)
                       ((long)plVar4 + *(long *)(*plVar4 + -0x18)));
    if (cVar2 != '\0') {
      std::operator<<((basic_ostream *)std::cout,"That\'s not a pair of numbers\n");
                    /* WARNING: Subroutine does not return */
      exit(1);
    }
    end_iter = std::
               map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
               ::end((
                      map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
                      *)pair_map);
    key_iter = std::
               map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
               ::find((
                       map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
                       *)pair_map,(int *)&num_key);
    cVar2 = std::operator==((_Rb_tree_iterator *)&key_iter,(_Rb_tree_iterator *)&end_iter);
                    /* this key doesn't have a map entry yet, create a vector for it */
    if (cVar2 != '\0') {
      end_iter = 0;
      local_3e0 = 0;
      local_3d8 = 0;
      std::vector<int,std::allocator<int>>::vector((vector<int,std::allocator<int>> *)&end_iter);
                    /* try { // try from 0010291f to 00102923 has its CatchHandler @ 00102ebf */
      pvVar6 = (vector<int,std::allocator<int>> *)
               std::
               map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
               ::operator[]((
                             map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
                             *)pair_map,(int *)&num_key);
      std::vector<int,std::allocator<int>>::operator=(pvVar6,(vector *)&end_iter);
      std::vector<int,std::allocator<int>>::~vector((vector<int,std::allocator<int>> *)&end_iter);
    }
    end_iter = std::
               map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
               ::end((
                      map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
                      *)pair_map);
                    /* try { // try from 00102972 to 00102976 has its CatchHandler @ 00102f90 */
    val_iter = std::
               map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
               ::find((
                       map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
                       *)pair_map,(int *)&num_val);
    cVar2 = std::operator==((_Rb_tree_iterator *)&val_iter,(_Rb_tree_iterator *)&end_iter);
                    /* this val doesn't have a map entry yet, create a vector for it */
    if (cVar2 != '\0') {
      end_iter = 0;
      local_3e0 = 0;
      local_3d8 = 0;
      std::vector<int,std::allocator<int>>::vector((vector<int,std::allocator<int>> *)&end_iter);
                    /* try { // try from 001029df to 001029e3 has its CatchHandler @ 00102ed6 */
      pvVar6 = (vector<int,std::allocator<int>> *)
               std::
               map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
               ::operator[]((
                             map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
                             *)pair_map,(int *)&num_val);
      std::vector<int,std::allocator<int>>::operator=(pvVar6,(vector *)&end_iter);
      std::vector<int,std::allocator<int>>::~vector((vector<int,std::allocator<int>> *)&end_iter);
    }
                    /* try { // try from 00102a1c to 00102a88 has its CatchHandler @ 00102f90 */
    pvVar6 = (vector<int,std::allocator<int>> *)
             std::
             map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
             ::operator[]((
                           map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
                           *)pair_map,(int *)&num_key);
    std::vector<int,std::allocator<int>>::push_back(pvVar6,(int *)&num_val);
    pvVar6 = (vector<int,std::allocator<int>> *)
             std::
             map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
             ::operator[]((
                           map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
                           *)pair_map,(int *)&num_val);
    std::vector<int,std::allocator<int>>::push_back(pvVar6,(int *)&num_key);
    pair_ctr = pair_ctr + 1;
  }
  std::
  map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
  ::map((
         map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
         *)&end_iter,pair_map);
                    /* try { // try from 00102a93 to 00102a97 has its CatchHandler @ 00102eed */
  cVar2 = compute(iVar1 - 1000);
  std::
  map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
  ::~map((
          map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
          *)&end_iter);
  if (cVar2 != '\0') {
    std::allocator<char>::allocator();
                    /* try { // try from 00102ad8 to 00102adc has its CatchHandler @ 00102f04 */
    std::__cxx11::basic_string<char,std::char_traits<char>,std::allocator<char>>::basic_string
              ((char *)local_398,(allocator *)&DAT_0010a06a);
    std::allocator<char>::~allocator((allocator<char> *)&end_iter);
    local_428 = pair_map;
    num_key = std::
              map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
              ::begin((
                       map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
                       *)local_428);
    num_val = std::
              map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
              ::end((
                     map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
                     *)local_428);
    while( true ) {
      cVar2 = std::operator!=((_Rb_tree_iterator *)&num_key,(_Rb_tree_iterator *)&num_val);
      if (cVar2 == '\0') break;
      ppVar7 = (pair *)std::
                       _Rb_tree_iterator<std::pair<int_const,std::vector<int,std::allocator<int>>>>
                       ::operator*((
                                    _Rb_tree_iterator<std::pair<int_const,std::vector<int,std::allocator<int>>>>
                                    *)&num_key);
                    /* try { // try from 00102b66 to 00102b6a has its CatchHandler @ 00102f7c */
      std::pair<int_const,std::vector<int,std::allocator<int>>>::pair
                ((pair<int_const,std::vector<int,std::allocator<int>>> *)&end_iter,ppVar7);
                    /* try { // try from 00102b7d to 00102b81 has its CatchHandler @ 00102f68 */
      std::__cxx11::to_string(local_378,(int)end_iter);
                    /* try { // try from 00102b9d to 00102ba1 has its CatchHandler @ 00102f2c */
      std::operator+((basic_string *)local_1c8,(char *)local_378);
                    /* try { // try from 00102bb6 to 00102bba has its CatchHandler @ 00102f18 */
      std::__cxx11::basic_string<char,std::char_traits<char>,std::allocator<char>>::operator+=
                (local_398,(basic_string *)local_1c8);
      std::__cxx11::basic_string<char,std::char_traits<char>,std::allocator<char>>::~basic_string
                ((basic_string<char,std::char_traits<char>,std::allocator<char>> *)local_1c8);
      std::__cxx11::basic_string<char,std::char_traits<char>,std::allocator<char>>::~basic_string
                ((basic_string<char,std::char_traits<char>,std::allocator<char>> *)local_378);
      local_420 = &local_3e0;
      key_iter = std::vector<int,std::allocator<int>>::begin
                           ((vector<int,std::allocator<int>> *)local_420);
      val_iter = std::vector<int,std::allocator<int>>::end
                           ((vector<int,std::allocator<int>> *)local_420);
      while( true ) {
        bVar3 = __gnu_cxx::operator!=((__normal_iterator *)&key_iter,(__normal_iterator *)&val_iter)
        ;
        if (bVar3 == false) break;
        piVar8 = (int *)__gnu_cxx::__normal_iterator<int*,std::vector<int,std::allocator<int>>>::
                        operator*((__normal_iterator<int*,std::vector<int,std::allocator<int>>> *)
                                  &key_iter);
        local_44c = *piVar8;
                    /* try { // try from 00102c61 to 00102c65 has its CatchHandler @ 00102f68 */
        std::__cxx11::to_string(local_378,local_44c);
                    /* try { // try from 00102c81 to 00102c85 has its CatchHandler @ 00102f54 */
        std::operator+((basic_string *)local_1c8,(char *)local_378);
                    /* try { // try from 00102c9a to 00102c9e has its CatchHandler @ 00102f40 */
        std::__cxx11::basic_string<char,std::char_traits<char>,std::allocator<char>>::operator+=
                  (local_398,(basic_string *)local_1c8);
        std::__cxx11::basic_string<char,std::char_traits<char>,std::allocator<char>>::~basic_string
                  ((basic_string<char,std::char_traits<char>,std::allocator<char>> *)local_1c8);
        std::__cxx11::basic_string<char,std::char_traits<char>,std::allocator<char>>::~basic_string
                  ((basic_string<char,std::char_traits<char>,std::allocator<char>> *)local_378);
        __gnu_cxx::__normal_iterator<int*,std::vector<int,std::allocator<int>>>::operator++
                  ((__normal_iterator<int*,std::vector<int,std::allocator<int>>> *)&key_iter);
      }
                    /* try { // try from 00102ce2 to 00102ce6 has its CatchHandler @ 00102f68 */
      std::__cxx11::basic_string<char,std::char_traits<char>,std::allocator<char>>::operator+=
                (local_398,"\n");
      std::pair<int_const,std::vector<int,std::allocator<int>>>::~pair
                ((pair<int_const,std::vector<int,std::allocator<int>>> *)&end_iter);
      std::_Rb_tree_iterator<std::pair<int_const,std::vector<int,std::allocator<int>>>>::operator++
                ((_Rb_tree_iterator<std::pair<int_const,std::vector<int,std::allocator<int>>>> *)
                 &num_key);
    }
    n = std::__cxx11::basic_string<char,std::char_traits<char>,std::allocator<char>>::length();
    d = (uchar *)std::__cxx11::basic_string<char,std::char_traits<char>,std::allocator<char>>::c_str
                           ();
                    /* try { // try from 00102d3b to 00102e37 has its CatchHandler @ 00102f7c */
    SHA1(d,n,digest_out);
    local_1c8[0] = 0x7c;
    local_1c8[1] = 0xba;
    local_1c8[2] = 0xdf;
    local_1c8[3] = 0xd3;
    local_1b8 = 9;
    local_1b4 = 0x7b;
    local_1b0 = 0x9c;
    local_1ac = 7;
    local_1a8 = 0x1b;
    local_1a4 = 0x86;
    local_1a0 = 0x76;
    local_19c = 0xed;
    local_198 = 0xac;
    local_194 = 0x38;
    local_190 = 0x12;
    local_18c = 0xf5;
    local_188 = 0x30;
    local_184 = 0x88;
    flag_pos = 0;
    while (flag_pos < 0x12) {
      std::operator<<((basic_ostream *)std::cout,digest_out[flag_pos] ^ (byte)local_1c8[flag_pos]);
      flag_pos = flag_pos + 1;
    }
                    /* WARNING: Subroutine does not return */
    exit(0);
  }
                    /* try { // try from 00102e59 to 00102e5d has its CatchHandler @ 00102f90 */
  std::operator<<((basic_ostream *)std::cout,"Wrong!\n");
  std::
  map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
  ::~map((
          map<int,std::vector<int,std::allocator<int>>,std::less<int>,std::allocator<std::pair<int_const,std::vector<int,std::allocator<int>>>>>
          *)pair_map);
  std::__cxx11::basic_stringstream<char,std::char_traits<char>,std::allocator<char>>::
  ~basic_stringstream((basic_stringstream<char,std::char_traits<char>,std::allocator<char>> *)
                      local_358);
  std::__cxx11::basic_string<char,std::char_traits<char>,std::allocator<char>>::~basic_string
            ((basic_string<char,std::char_traits<char>,std::allocator<char>> *)inp);
  if (local_20 != *(long *)(in_FS_OFFSET + 0x28)) {
                    /* WARNING: Subroutine does not return */
    __stack_chk_fail();
  }
  return 0;
}

