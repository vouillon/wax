(module
  (rec
    (type $a (sub final (descriptor $b) (struct)))
    (type $b (sub (describes $a) (struct))))
  (global (export "g") (ref null $a) (ref.null $a)))
