(module
  (rec
    (type $a (sub (struct)))
    (type $b (sub $a (descriptor $b_desc) (struct)))
    (type $b_desc (sub (describes $b) (struct)))))
