Fix_sub {_ : nat -> nat -> nat & {_ : patriciaTree & patriciaTree}}
  (MR lt
     (fun recarg : {_ : nat -> nat -> nat & {_ : patriciaTree & patriciaTree}} =>
      nodes (projT1 (projT2 recarg)) + nodes (projT2 (projT2 recarg))))
  merge_func_obligation_12
  (fun _ : {_ : nat -> nat -> nat & {_ : patriciaTree & patriciaTree}} => patriciaTree)
  (fun (recarg : {_ : nat -> nat -> nat & {_ : patriciaTree & patriciaTree}})
     (merge' : {recarg' : {_ : nat -> nat -> nat & {_ : patriciaTree & patriciaTree}}
               | nodes (projT1 (projT2 recarg')) + nodes (projT2 (projT2 recarg')) <
                 nodes (projT1 (projT2 recarg)) + nodes (projT2 (projT2 recarg))} ->
               patriciaTree) =>
   match
     projT1 (projT2 recarg) as t'
     return
   (t' = projT1 (projT2 recarg) ->
        projT2 (projT2 recarg) = projT2 (projT2 recarg) -> patriciaTree)
   with
   | empty =>
       fun (_ : empty = projT1 (projT2 recarg))
         (_ : projT2 (projT2 recarg) = projT2 (projT2 recarg)) =>
       projT2 (projT2 recarg)
   | leaf k x =>
       match
         projT2 (projT2 recarg) as s'
         return
           (leaf k x = projT1 (projT2 recarg) ->
            s' = projT2 (projT2 recarg) -> patriciaTree)
       with
       | empty =>
           fun (_ : leaf k x = projT1 (projT2 recarg))
             (_ : empty = projT2 (projT2 recarg)) => projT1 (projT2 recarg)
       | leaf k0 x0 =>
   fun (_ : leaf k x = projT1 (projT2 recarg))
             (_ : leaf k0 x0 = projT2 (projT2 recarg)) =>
           insert (projT1 recarg) k x (projT2 (projT2 recarg))
       | trie n n0 p p0 =>
           fun (_ : leaf k x = projT1 (projT2 recarg))
             (_ : trie n n0 p p0 = projT2 (projT2 recarg)) =>
           insert (projT1 recarg) k x (projT2 (projT2 recarg))
       end
   | trie p m s0 s1 =>
       match
         projT2 (projT2 recarg) as s'
         return
           (trie p m s0 s1 = projT1 (projT2 recarg) ->
            s' = projT2 (projT2 recarg) -> patriciaTree)
       with
       | empty =>
           fun (_ : trie p m s0 s1 = projT1 (projT2 recarg))
             (_ : empty = projT2 (projT2 recarg)) => projT1 (projT2 recarg)
       | leaf k x =>
           fun (_ : trie p m s0 s1 = projT1 (projT2 recarg))
             (_ : leaf k x = projT2 (projT2 recarg)) =>
           insert (swap (projT1 recarg)) k x (projT2 (projT2 recarg))
       | trie q n t0 t3 =>
           fun (Heq_s : trie p m s0 s1 = projT1 (projT2 recarg))
             (Heq_t : trie q n t0 t3 = projT2 (projT2 recarg)) =>
           if (m =? n)%N && (p =? q)%N
           then
            trie p m
              (merge'
                 (exist
                    (fun
                       recarg' : {_ : nat -> nat -> nat &
                                 {_ : patriciaTree & patriciaTree}} =>
                     nodes (projT1 (projT2 recarg')) + nodes (projT2 (projT2 recarg')) <
                     nodes (projT1 (projT2 recarg)) + nodes (projT2 (projT2 recarg)))
                    (existT
                       (fun _ : nat -> nat -> nat => {_ : patriciaTree & patriciaTree})
                       (projT1 recarg)
                       (existT (fun _ : patriciaTree => patriciaTree) s0 t0))
                    (merge_func_obligation_1 (projT1 (projT2 recarg))
                       (projT2 (projT2 recarg))
                       (fun (c0 : nat -> nat -> nat) (s t : patriciaTree)
                          (recproof : nodes s + nodes t <
                                      nodes (projT1 (projT2 recarg)) +
                                      nodes (projT2 (projT2 recarg))) =>
                        merge'
                          (exist
                             (fun
                                recarg' : {_ : nat -> nat -> nat &
                                          {_ : patriciaTree & patriciaTree}} =>
                              nodes (projT1 (projT2 recarg')) +
                              nodes (projT2 (projT2 recarg')) <
                              nodes (projT1 (projT2 recarg)) +
                              nodes (projT2 (projT2 recarg)))
                             (existT
                                (fun _ : nat -> nat -> nat =>
                                 {_ : patriciaTree & patriciaTree}) c0
                                (existT (fun _ : patriciaTree => patriciaTree) s t))
                             recproof)) p m s0 s1 q n t0 t3 Heq_s Heq_t)))
              (merge'
                 (exist
                    (fun
                       recarg' : {_ : nat -> nat -> nat &
                                 {_ : patriciaTree & patriciaTree}} =>
                     nodes (projT1 (projT2 recarg')) + nodes (projT2 (projT2 recarg')) <
                     nodes (projT1 (projT2 recarg)) + nodes (projT2 (projT2 recarg)))
                    (existT
                       (fun _ : nat -> nat -> nat => {_ : patriciaTree & patriciaTree})
                       (projT1 recarg)
                       (existT (fun _ : patriciaTree => patriciaTree) s1 t3))
                    (merge_func_obligation_2 (projT1 (projT2 recarg))
                       (projT2 (projT2 recarg))
                       (fun (c0 : nat -> nat -> nat) (s t : patriciaTree)
                          (recproof : nodes s + nodes t <
                                      nodes (projT1 (projT2 recarg)) +
                                      nodes (projT2 (projT2 recarg))) =>
                        merge'
                          (exist
                             (fun
                                recarg' : {_ : nat -> nat -> nat &
                                          {_ : patriciaTree & patriciaTree}} =>
                              nodes (projT1 (projT2 recarg')) +
                              nodes (projT2 (projT2 recarg')) <
                              nodes (projT1 (projT2 recarg)) +
                              nodes (projT2 (projT2 recarg)))
                             (existT
                                (fun _ : nat -> nat -> nat =>
                                 {_ : patriciaTree & patriciaTree}) c0
                                (existT (fun _ : patriciaTree => patriciaTree) s t))
                             recproof)) p m s0 s1 q n t0 t3 Heq_s Heq_t)))
           else
            if (m <? n)%N && matchPrefix q p m
            then
             if zeroBit q m
             then
              br p m
                (merge'
                   (exist
                      (fun
                         recarg' : {_ : nat -> nat -> nat &
                                   {_ : patriciaTree & patriciaTree}} =>
                       nodes (projT1 (projT2 recarg')) +
                       nodes (projT2 (projT2 recarg')) <
                       nodes (projT1 (projT2 recarg)) + nodes (projT2 (projT2 recarg)))
                      (existT
                         (fun _ : nat -> nat -> nat =>
                          {_ : patriciaTree & patriciaTree}) 
                         (projT1 recarg)
                         (existT (fun _ : patriciaTree => patriciaTree) s0
                            (projT2 (projT2 recarg))))
                      (merge_func_obligation_3 (projT1 (projT2 recarg))
                         (projT2 (projT2 recarg))
                         (fun (c0 : nat -> nat -> nat) (s t : patriciaTree)
                            (recproof : nodes s + nodes t <
                                        nodes (projT1 (projT2 recarg)) +
                                        nodes (projT2 (projT2 recarg))) =>
                          merge'
                            (exist
                               (fun
                                  recarg' : {_ : nat -> nat -> nat &
                                            {_ : patriciaTree & patriciaTree}} =>
                                nodes (projT1 (projT2 recarg')) +
                                nodes (projT2 (projT2 recarg')) <
                                nodes (projT1 (projT2 recarg)) +
                                nodes (projT2 (projT2 recarg)))
                               (existT
                                  (fun _ : nat -> nat -> nat =>
                                   {_ : patriciaTree & patriciaTree}) c0
                                  (existT (fun _ : patriciaTree => patriciaTree) s t))
                               recproof)) p m s0 s1 q n t0 t3 Heq_s Heq_t))) s1
             else
              br p m s0
                (merge'
                   (exist
                      (fun
                         recarg' : {_ : nat -> nat -> nat &
                                   {_ : patriciaTree & patriciaTree}} =>
                       nodes (projT1 (projT2 recarg')) +
                       nodes (projT2 (projT2 recarg')) <
                       nodes (projT1 (projT2 recarg)) + nodes (projT2 (projT2 recarg)))
                      (existT
                         (fun _ : nat -> nat -> nat =>
                          {_ : patriciaTree & patriciaTree}) 
                         (projT1 recarg)
                         (existT (fun _ : patriciaTree => patriciaTree) s1
                            (projT2 (projT2 recarg))))
                      (merge_func_obligation_4 (projT1 (projT2 recarg))
                         (projT2 (projT2 recarg))
                         (fun (c0 : nat -> nat -> nat) (s t : patriciaTree)
                            (recproof : nodes s + nodes t <
                                        nodes (projT1 (projT2 recarg)) +
                                        nodes (projT2 (projT2 recarg))) =>
                          merge'
                            (exist
                               (fun
                                  recarg' : {_ : nat -> nat -> nat &
                                            {_ : patriciaTree & patriciaTree}} =>
                                nodes (projT1 (projT2 recarg')) +
                                nodes (projT2 (projT2 recarg')) <
                                nodes (projT1 (projT2 recarg)) +
                                nodes (projT2 (projT2 recarg)))
                               (existT
                                  (fun _ : nat -> nat -> nat =>
                                   {_ : patriciaTree & patriciaTree}) c0
                                  (existT (fun _ : patriciaTree => patriciaTree) s t))
                               recproof)) p m s0 s1 q n t0 t3 Heq_s Heq_t)))
            else
             if (n <? m)%N && matchPrefix p q n
             then
              if zeroBit p n
              then
               br q n
                 (merge'
                    (exist
                       (fun
                          recarg' : {_ : nat -> nat -> nat &
                                    {_ : patriciaTree & patriciaTree}} =>
                        nodes (projT1 (projT2 recarg')) +
                        nodes (projT2 (projT2 recarg')) <
                        nodes (projT1 (projT2 recarg)) + nodes (projT2 (projT2 recarg)))
                       (existT
                          (fun _ : nat -> nat -> nat =>
                           {_ : patriciaTree & patriciaTree}) 
                          (projT1 recarg)
                          (existT (fun _ : patriciaTree => patriciaTree)
                             (projT1 (projT2 recarg)) t0))
                       (merge_func_obligation_5 (projT1 (projT2 recarg))
                          (projT2 (projT2 recarg))
                          (fun (c0 : nat -> nat -> nat) (s t : patriciaTree)
                             (recproof : nodes s + nodes t <
                                         nodes (projT1 (projT2 recarg)) +
                                         nodes (projT2 (projT2 recarg))) =>
                           merge'
                             (exist
                                (fun
                                   recarg' : {_ : nat -> nat -> nat &
                                             {_ : patriciaTree & patriciaTree}} =>
                                 nodes (projT1 (projT2 recarg')) +
                                 nodes (projT2 (projT2 recarg')) <
                                 nodes (projT1 (projT2 recarg)) +
                                 nodes (projT2 (projT2 recarg)))
                                (existT
                                   (fun _ : nat -> nat -> nat =>
                                    {_ : patriciaTree & patriciaTree}) c0
                                   (existT (fun _ : patriciaTree => patriciaTree) s t))
                                recproof)) p m s0 s1 q n t0 t3 Heq_s Heq_t))) t3
              else
               br q n t0
                 (merge'
                    (exist
                       (fun
                          recarg' : {_ : nat -> nat -> nat &
                                    {_ : patriciaTree & patriciaTree}} =>
                        nodes (projT1 (projT2 recarg')) +
                        nodes (projT2 (projT2 recarg')) <
                        nodes (projT1 (projT2 recarg)) + nodes (projT2 (projT2 recarg)))
                       (existT
                          (fun _ : nat -> nat -> nat =>
                           {_ : patriciaTree & patriciaTree}) 
                          (projT1 recarg)
                          (existT (fun _ : patriciaTree => patriciaTree)
                             (projT1 (projT2 recarg)) t3))
                       (merge_func_obligation_6 (projT1 (projT2 recarg))
                          (projT2 (projT2 recarg))
                          (fun (c0 : nat -> nat -> nat) (s t : patriciaTree)
                             (recproof : nodes s + nodes t <
                                         nodes (projT1 (projT2 recarg)) +
                                         nodes (projT2 (projT2 recarg))) =>
                           merge'
                             (exist
                                (fun
                                   recarg' : {_ : nat -> nat -> nat &
                                             {_ : patriciaTree & patriciaTree}} =>
                                 nodes (projT1 (projT2 recarg')) +
                                 nodes (projT2 (projT2 recarg')) <
                                 nodes (projT1 (projT2 recarg)) +
                                 nodes (projT2 (projT2 recarg)))
                                (existT
                                   (fun _ : nat -> nat -> nat =>
                                    {_ : patriciaTree & patriciaTree}) c0
                                   (existT (fun _ : patriciaTree => patriciaTree) s t))
                                recproof)) p m s0 s1 q n t0 t3 Heq_s Heq_t)))
             else join p q (projT1 (projT2 recarg)) (projT2 (projT2 recarg))
       end
   end eq_refl eq_refl)
  (existT (fun _ : nat -> nat -> nat => {_ : patriciaTree & patriciaTree}) c
     (existT (fun _ : patriciaTree => patriciaTree) t1 t2))
