(ns hello.4clojure)

(defn count-occurances
  [sequence]
  (let [identity-map (group-by identity sequence)
        id-map-keys  (keys identity-map)
        id-map-vals  (vals identity-map)
        count-vals   (map count id-map-vals)]
    (zipmap id-map-keys count-vals)))

(defn find-distinct
  [sequence]
  (loop [distinct-element-seq '[]
         identity-set         #{}
         remaining-seq        (map first (partition-by identity sequence))]
    (if (empty? remaining-seq) ;; return the result if we traversed the entire sequence
      distinct-element-seq 
      (let [next-element (first remaining-seq)
            distinct-element-seq'
            (if (contains? identity-set next-element) ;; only add an element to the
              ;; result if it has not been encountered before
              distinct-element-seq
              (conj distinct-element-seq next-element))
            identity-set' (conj identity-set next-element)
            remaining-seq' (rest remaining-seq)]
        (recur distinct-element-seq' identity-set' remaining-seq')))))

(defn function-comp
  "Takes the argument list and reverses it,
  then reduces the list by creating a higher order
  function where the second function in the list
  is called on the first function, which is applied 
  on a list of arguments. The list of arguments is important
  because it allows the rightmost function in the function list
  to be a function which takes multiple arguments, for example
  +."
  [& functions]
  (reduce #(fn [& x] (%2 (apply %1 x))) (reverse functions)))

(defn juxtaposition
  [& functions]
  (fn [& x]
    (into '[]
          (for [f functions]
            (apply f x)))))

(defn my-reductions
  ([f se]
   (my-reductions f (first se) (rest se))) ;; if no init specified, call the same function
  ;; but with the init parameter
  ([f first-arg se]
   (letfn [(reduct [f init remaining-se]
             (lazy-seq (when (not-empty remaining-se)
                         (let [res (f init (first remaining-se))]
                           (cons res (reduct f res (rest remaining-se)))))))] ;; lazy recipe
     ;; recursive call with the result being the new init
     (lazy-seq (cons first-arg (reduct f first-arg se))))))

(defn my-iterate
  [f x]
  (lazy-seq (cons x (my-iterate f (f x))))) ;; lazy recipe

(defn my-group-by
  [f coll]
  (letfn
      [(reduce-coll [f map se]
         (if (not-empty se)
           (let [next-element (first se)
                 result (f next-element)
                 new-map (update-in map [result] #(conj (into [] %1) %2) next-element)]
             ;; associate the result with the function-input-value which lead to it
             ;; sequentially using the next value in se
             (reduce-coll f new-map (rest se))) ;; recursive call if more inputs exist
           map))] ;; base case
    (reduce-coll f {} coll)))

(defn black-box
  [coll]
  (let [test-pair [:a :a]
        test-pair-2 [:b :b]]
    (letfn [(not-nil? [item]
              (not (nil? item)))
            (test-list [given-coll]
              (= test-pair-2 (first (conj given-coll test-pair test-pair-2))))
            (test-vec [given-coll]
              (= test-pair-2 (last (conj given-coll test-pair test-pair-2))))
            (test-map [given-coll]
              (= given-coll (merge given-coll given-coll)))
            (test-set [given-coll]
              (not-nil? (get (conj given-coll test-pair) test-pair)))]
      (cond ;; map and set branch first because map may also
        ;; return true for the vector test
        (test-map coll) :map
        (test-set coll) :set
        (test-list coll) :list
        (test-vec coll) :vector))))

(defn gcd
  [num1 num2]
  (loop [dividend (max num1 num2)
         divisor (min num1 num2)
         quotient (quot dividend divisor)
         remainder (rem dividend divisor)]
    (if (= 0 remainder)
      divisor
      (recur divisor remainder (quot divisor remainder) (rem divisor remainder)))))

(defn primes
  [n] ;; naive / first approach without a sieve
  (take n (filter #(loop [x 2]
                     (if (= x %)
                       true
                       (if (or (< % 2) (= 0 (rem % x)))
                         false
                         (recur (inc x))))) (range))))

(defn prime-sieve
  []
  (letfn [(next-composite [composite-map x]
            (if-let [composite-prime-set (composite-map x)]
              (merge-with clojure.set/union composite-map
                          (into {} (map #(vector (+ x %) #{%}) composite-prime-set)))
              (assoc composite-map (+ x x) #{x})))
          (create-lazy [x composite-map]
            (let [composite-prime (composite-map x)
                  prime? (nil? composite-prime)
                  composite-map (next-composite composite-map x)
                  composite-map (dissoc composite-map x)]
              (if prime?
                (lazy-seq (cons x (create-lazy (+ x 1) composite-map)))
                (recur (+ x 1) composite-map))))]
    (lazy-seq (create-lazy 2 {})))) 

(defn prime-sieve2
  []
  (letfn
      [(next-composite [composite-map n step]
         (if (composite-map n)
           (recur composite-map (+ n step) step)
           (let [final-value (if (= n step) (+ n step) n)]
             (assoc composite-map final-value step))))
       (next-prime
         [n composite-map]
         (let [prime-factor (composite-map n)
               prime? (nil? prime-factor)
               step (if prime-factor prime-factor n) 
               composite-map (next-composite composite-map n step)
               composite-map (dissoc composite-map n)]
           (if prime?
             (lazy-seq (cons n (next-prime (+ n 1) composite-map)))
             (recur (+ n 1) composite-map))))]
    (lazy-seq (next-prime 2 {}))))

(defn prime-sieve3
  []
  (letfn
      [(next-composite [composite-map n step]
         (if (composite-map n)
           (recur composite-map (+ n step step) step)
           (let [final-value (if (= n step) (+ n step step) n)]
             (assoc composite-map final-value step))))
       (next-prime
         [n composite-map]
         (let [prime-factor (composite-map n)
               prime? (nil? prime-factor)
               step (if prime-factor prime-factor n) 
               composite-map (next-composite composite-map n step)
               composite-map (dissoc composite-map n)]
           (if prime?
             (lazy-seq (cons n (next-prime (+ n 2) composite-map)))
             (recur (+ n 2) composite-map))))]
    (lazy-seq (cons 2 (next-prime 3 {})))))


(defn next-composite [composite-map x]
  (let [composite-primes (composite-map x)
        new-composites (into {} (map #(vector (+ x %) #{%}) composite-primes))]
    (if composite-primes
      (merge-with clojure.set/union composite-map new-composites)

      (assoc composite-map (+ x x) #{x}))))

(defn my-merge-with [f first-map & maps]
  (let [key-and-bindings
        (group-by first (apply concat [] first-map maps))] ;; groups each key with its corresponding bindings
    (into {} (map #(vector
                    (first %)
                    (reduce f (map second (second %)))) key-and-bindings)))) ;; reduces the values in the bidings
;; using the given function. Binds the keys to the single reduced values.

;; an all manual solution to sorting words
(defn word-sort [sentence]
  (letfn [(char-index [character] ;; this is used for getting the index of a letter in the alphabet
            ;; regardless of case (upper / lower)
            (let [char-value (int character)]
              (if (and (>= char-value 65) (<= char-value 90))
                (- char-value 64)
                (- char-value 96))))
          (compare-words [word-a word-b] ;; this is a recursive function used to compare two
            ;; words. Returns -1 if first word lower alphabetically, 0 if the same, 1 if higher
            (cond (every? empty? [word-a word-b])
                  0
                  (empty? word-a)
                  -1
                  (empty? word-b)
                  1
                  (> (char-index (first word-a)) (char-index (first word-b)))
                  1
                  (< (char-index (first word-a)) (char-index (first word-b)))
                  -1
                  :else
                  (recur (rest word-a) (rest word-b))))
          (quick-sort-words [col] ;; quicksort as a tree of lists
            (let [pivot (last col)]
              (letfn [(filter-left [word]
                        (= -1 (compare-words word pivot)))
                      (filter-right [word]
                        (= 1 (compare-words word pivot)))]
                (if (<= (count col) 1)
                  col
                  (list (quick-sort-words (filter filter-left col))
                        (quick-sort-words (cons pivot (filter filter-right col))))))))]
    (let [words (re-seq #"[a-zA-z]+" sentence)]
      (flatten (quick-sort-words words)))))

(concat [] {:a 1} {:a 1 :b 2})

(defn compare-words [word-a word-b]
  (letfn [(char-index [character]
            (let [char-value (int character)]
              (if (and (>= char-value 65) (<= char-value 90))
                (- char-value 64)
                (- char-value 96))))]
    (cond (every? empty? [word-a word-b])
          0
          (empty? word-a)
          -1
          (empty? word-b)
          1
          (> (char-index (first word-a)) (char-index (first word-b)))
          1
          (< (char-index (first word-a)) (char-index (first word-b)))
          -1
          :else
          (recur (rest word-a) (rest word-b)))))


(defn quick-sort
  [col]
  (let [pivot (last col)]
    (letfn [(filter-left [x]
              (< x pivot))
            (filter-right [x]
              (> x pivot))]
      (if (<= (count col) 1)
        col
        (list (quick-sort (filter filter-left col)) (quick-sort (cons pivot (filter filter-right col))))))))

(defn tic-tac-toe
  "Returns the winner :x, :o, or nil, for an arbitrary tic-tac-toe board."
  [board]
  (let [x :x o :o]
    (letfn [(horizontal-check
              [board]
              (filter
               #(not (nil? %))
               (map #(cond (every? (partial = x) %)
                           x
                           (every? (partial = o) %)
                           o) board)))
            (invert-board
              [board]
              (if (seq (flatten board))
                (cons (map first board) (invert-board (map rest board)))))
            (diagonal
              [board]
              (if (seq (flatten board))
                (cons (ffirst board) (diagonal (rest (map rest board))))))]
      ((juxt
        horizontal-check
        (comp horizontal-check invert-board)
        (comp horizontal-check #(into [] %) #(map vector %) diagonal)
        (comp horizontal-check #(into [] %) #(map vector %) diagonal #(map reverse %))) board))))

(defn filter-perfect-squares
  [string]
  "Take a string with a sequence of numbers represented in it e.g. 'x1,x2,x3,x4,...xn'
  Return a new string containing only the perfect squares represented by the original string."
  (let [given-seq (map #(Integer/parseInt %) (re-seq #"\d+" string))
        max-number (apply max given-seq)
        predicate (into
                   #{}
                   (take-while #(<= % max-number) ((fn squares
                                                     [x] (lazy-seq (cons (* x x) (squares (inc x))))) 1)))]
    (reduce #(str %1 "," %2) (filter predicate given-seq))))

(defn totient
  "The number of natural numbers less than x which are co-primes of x"
  [x]
  (letfn [(gcd [a b]
            (cond
              (= a b)
              a
              (> a b)
              (recur (- a b) b)
              (< a b)
              (recur a (- b a))))]
    (if (= x 1)
      1
      (count (filter #{1} (map #(gcd % x) (range 1 x)))))))

(defn anagram-finder
  "Returns a set of sets of words (at least 2) which are anagrams of each other,
  given a sentence."
  [word-vector]
  (->> (reduce #(update-in %1 [(into #{} %2)] (fn [myset] (conj myset %2))) (cons {} word-vector))
       ;; associate hash-sets of chars with a sets of their corresponding words in a map
       vals
       (map #(into #{} %))
       (filter #(> (count %) 1))
       (into #{})))

(defn my-trampoline
  "Takes a given function f and an arbitrary number of arguments.
  If f returns a function, call that function with no arguments.
  Otherwise return the final value.
  Useful for calling mutually recursive functions without consuming
  the stack."
  [f & args]
  (if (fn? f)
    (let [result (apply f args)]
      (if (fn? result)
        (my-trampoline result)
        result))))

(defn triangle-min-path
  "Finds the sum of the minimal path of a triangle (sequence of vectors
  beginning at 1 length, increasing by 1 each for an arbitrary length)."
  [triangle]
  (letfn [(min-pairs [col acc]
            (if (> (count col) 1)
              (recur (rest col) (conj acc (apply min (take 2 col))))
              acc))]
    (loop [remaining-triangle triangle]
      (if (= (count remaining-triangle) 1)
        (ffirst remaining-triangle)
        (recur (conj
                (into [] (drop-last 2 remaining-triangle))
                (mapv
                 +
                 (first (take-last 2 remaining-triangle))
                 (min-pairs (last remaining-triangle) []))))))))

;; An overly complicated solution
(defn perfect-number-c?
  "Returns true if n is a perfect number. I.e. the sum of its divisors
   is equal to itself."
  [n]
  (letfn [(next-composite
            [n step composite-map]
            (if (composite-map (+ n step step))
              (next-composite (+ n step step) step composite-map)
              (+ n step step)))
          (primes-lazy
            [n composite-map]
            (lazy-seq
             (if-let [step (composite-map n)]
               (primes-lazy
                (+ n 2)
                (assoc composite-map (next-composite n step composite-map) step))
               (cons n (primes-lazy
                        (+ 2 n)
                        (assoc composite-map (* 3 n) n))))))
          (prime-divisors
            [x divisor-seq]
            (filter
             #(= 0 (mod x %))
             (cons 2 (take-while #(<= % x) (primes-lazy 3 {})))))]
    (= n (- (->>
             (prime-divisors n [])
             (map #((fn [x power base]
                      (if (and (<= x n) (= 0 (mod n x)))
                        (recur (* x base) (inc power) base)
                        (vector % power))) % 0 %))
             (map #(let [n (first %)
                         e (second %)]
                     (if (> e 1)
                       (dec (apply * (repeat (inc e) n)))
                       (inc n))))
             (apply *)) n))))

(defn perfect-number?
  [n]
  (->>
   (range 1 n)
   (filter #(= 0 (rem n %)))
   ((comp (partial = n) (partial reduce +)))))

(defn my-intersection
  [set-a set-b]
  (->>
   (map #(set-b %) set-a)
   (filter some?)
   (into #{})))

(defn word-chain?
  [word-set]
  (letfn [(strings-info
            [a b]
            (let [longer (if (> (count a) (count b)) a b)
                  shorter (if (= longer a) b a)
                  equal? (= longer shorter)
                  count-diff (- (count longer) (count shorter))]
              [longer shorter equal? count-diff]))
          (letter-apart?
            [a b]
            (let [info-v (strings-info a b)]
              (cond (info-v 2)
                    false
                    (> (last info-v) 1)
                    false
                    :else
                    (loop [longer (first info-v)
                           shorter (second info-v)]
                      (if (= (first longer) (first shorter))
                        (recur (rest longer) (rest shorter))
                        (if (zero? (last info-v))
                          (= (rest longer) (rest shorter))
                          (= (apply str (rest longer)) (apply str shorter))))))))
          (set-permutations
            [word-set & acc]
            (map
             #(if (= 1 (count word-set))
                (reduce (fn [a b] (cond (false? a) false
                                       (letter-apart? a b) b
                                       :else false)) (flatten (conj acc %)))
                (set-permutations (disj word-set %) (cons % acc))) word-set))]
    (true? (some string? (flatten (set-permutations word-set))))))

(defn half-truth?
  [& coll]
  (= #{true false} (into #{} (distinct coll))))

(defn transitive-binary
  [tuple-set]
  (let [tuple-first-map
        (into {} (map #(vector (first %) %) tuple-set))]
    (loop [remaining-ts tuple-set
           acc-set #{}]
      (let [current-tuple (first remaining-ts)
            tr-candidate (if (tuple-first-map (second current-tuple))
                                   (vector
                                    (first current-tuple)
                                    (second (tuple-first-map (second current-tuple)))))
            tr-closure
            (if (and tr-candidate (not (acc-set tr-candidate)))
              tr-candidate)
            remaining-ts' (disj (if tr-closure
                            (conj remaining-ts tr-closure)
                            remaining-ts) current-tuple)]
        (if (seq remaining-ts)
          (recur remaining-ts' (conj acc-set current-tuple))
          acc-set)))))

(defn power-set
  [original-set]
  (letfn [(pow [a b] (apply * (repeat b a)))
          (binary-vector
            [n v]
            (let [powers-2 (into [] (for [i (range (count v))]
                                      (assoc v (- (dec (count v)) i) 1)))]
              (loop [remaining-n n v' v]
                (let [remaining-n' (last (take-while #(>= remaining-n (pow 2 %)) (range)))
                      v' (mapv + v' (powers-2 remaining-n'))
                      remaining-n' (- remaining-n (pow 2 remaining-n'))]
                  (if (pos? remaining-n')
                    (recur remaining-n' v')
                    v')))))]
    (let [elements (into [] original-set)
          zero-vector
          (into [] (map (constantly 0) elements))
          binary-numbers
          (cons
           zero-vector
           (map (memoize #(binary-vector % zero-vector))
                (range 1 (pow 2 (count elements)))))]
      (set (for [number binary-numbers]
             (set (filter
                   (comp not nil?)
                   (map #(if (= (number %) 1) (elements %)) (range (count number))))))))))

(defn happy-number?
  [n]
  (letfn [(happy
            [n n-seen]
            (if (or (= 1 n) (n-seen n))
              n
              (let [n' (reduce + (map (comp
                                       #(* % %)
                                       #(Integer/parseInt %)) (map str (str n))))]
                (happy n' (conj n-seen n)))))]
    (if (= 1 (happy n #{})) true false)))

(defn symmetric-difference
  [a b]
  (let [union (into a b)]
    (into (apply disj union a) (apply disj union b))))

(defn graph-tour-possible?
  [graph]
  (letfn [(next-struct [current-struct next-idx]
            (assoc current-struct
                   0 (next-node (current-struct 0) (graph next-idx))
                   1 (disj (current-struct 1) next-idx)
                   2 (conj (current-struct 2) (graph next-idx))))
          (next-node [last-node edge]
            (cond (= last-node (first edge)) (second edge)
                  (= last-node (second edge)) (first edge)
                  :else nil))
          (edge-struct [first-idx v]
            (vector (v (- 1 first-idx)) (set (range 0 (count graph))) (list) (v first-idx) v))]
    (let [first-queue (concat (map (partial edge-struct 0) graph) (map (partial edge-struct 1) graph))]
      (loop [queue first-queue]
        (let [current-struct (first queue)
              possible? (and (empty? (current-struct 1))
                             (= (current-struct 4) (vector (current-struct 0) (current-struct 3))))
              queue-addition (remove #(nil? (first %))
                                     (map (partial next-struct current-struct) (current-struct 1)))]
          (if (or (= 1 (count queue)) possible?)
            (or possible? (= 1 (count graph)))
            (recur (if (seq queue-addition) (apply conj (rest queue) queue-addition) (rest queue)))))))))

(defn connected-graph?
  [graph]
  (loop [edges #{(first graph)}
         nodes (set (first graph)) 
         remaining-edges (disj graph (first graph))]
    (if-let [edges-addition
             (seq (remove nil? (map #(if (some identity (map nodes %)) %)
                                    remaining-edges)))]
      (recur (apply conj edges edges-addition)
             (apply conj nodes (flatten edges-addition))
             (apply disj remaining-edges edges-addition))
      (empty? remaining-edges))))

(defn roman-numerals
  [string]
  (let [subtracted {"IV" 4 "IX" 9 "XL" 40 "XC" 90 "CD" 400 "CM" 900}
        values {"I" 1 "V" 5 "X" 10 "L" 50 "C" 100 "D" 500 "M" 1000}]
    (loop [remaining-string string
           sum 0]
      (if-let [subtract (subtracted (apply str (take 2 remaining-string)))]
        (recur (drop 2 remaining-string) (+ sum subtract))
        (if (seq remaining-string)
          (recur (rest remaining-string) (+ sum (values (str (first remaining-string)))))
          sum)))))

(defn partial-flatten
  [coll]
  (let [flatten-level
        (apply concat (map (fn [e] (if (and (coll? e) (some coll? e)) e (list e))) coll))]
    (if (every? (complement coll?) (apply concat flatten-level))
      flatten-level
      (recur flatten-level))))

(defn game-of-life
  [board]
  (let [rows (count board)
        columns (count (first board))
        cell (fn [x y] (if (and (<= 0 x (dec columns))
                               (<= 0 y (dec rows)))
                        (nth (board y) x)))
        neighbor-xy (list [0 -1] [0 1] [-1 0] [1 0] [-1 -1] [-1 1] [1 -1] [1 1])
        neighbors (fn [x y]
                    (map #(cell (+ x (% 0)) (+ y (% 1))) neighbor-xy))]
    (->> (for [y (range 0 rows)
               x (range 0 columns)]
           (vector (cell x y) (count (filter #{\#} (neighbors x y)))))
         (map #(if (or (and (= \# (% 0)) (<= 2 (% 1) 3))
                       (and (= \space (% 0)) (= 3 (% 1)))) \# \space))
         (partition columns)
         (map #(apply str %)))))

(defn binary-tree?
  [tree]
  (letfn [(f [t parent]
            (if (and (= 3 (count t)) (first t) (every? nil? (rest t)))
              nil
              (if (not= t parent)
                (f (map #(if (sequential? %) (f % t) %) t) t)
                false)))]
    (and (sequential? tree) (not (nil? tree)) (nil? (f tree nil)))))

;; another solution
;; I was not used to using recursion in this way in Clojure yet:
;; i.e. invoking a recursive function more than once in one expression other than map
(defn binary-tree?
  [tree]
  (let [next-fn (fn [x] (or (nil? x) (and (sequential? x) (binary-tree? x))))]
  (if (and (first tree) (= 3 (count tree)))
    (and (next-fn (second tree)) (next-fn (last tree)))
    false)))

;; At first I did not use the form [v l r] in the arguments for f.
;; At that point I was not used to binding parts of an argument
;; to id's within the argument vector. This new function saved some lines of code.
(defn symmetrical-binary-tree?
  [tree]
  (letfn [(f [[v l r]]
            (list
             v
             (if (sequential? l) (f (list (first l) (last l) (second l))) l)
             (if (sequential? r) (f (list (first r) (last r) (second r))) r)))]
    (let [tree' (f tree)]
      (= (second tree') (last tree'))
      (and (= (second tree') (last tree)) (= (second tree) (last tree'))))))

(defn pascals-triangle
  [n]
  (letfn [(f [row rem-iterations]
            (if (> rem-iterations 1)
              (recur
               (concat [1] (map
                            #(+ (nth row %) (nth row (inc %)))
                            (range 0 (dec (count row)))) [1]) (dec rem-iterations))
              row))]
    (f [1] n)))

(defn equivilance-classes
  [f coll]
  (set (map set (vals (group-by f coll)))))

(defn product-digits
  [a b]
  (mapv #(- (int %) 48) ((comp str *) a b)))

(defn lcm
  [& ns]
  (letfn [(prime-factors [n]
            (filter
             #(and (zero? (rem n %)) (every? (fn [x] (not= 0 (rem % x))) (range 2 %)))
             (range 2 (inc n))))]
    (apply * (set (prime-factors (reduce * ns))))))

(defn lcm
  [& ns]
  (reduce (fn [a b]
            (first (drop-while #(or (not= 0 (rem % a))
                                    (not= 0 (rem % b))) (iterate (partial + a) a)))) ns))

;;http://people.cs.pitt.edu/~kirk/cs1501/Pruhs/Fall2006/Assignments/editdistance/Levenshtein%20Distance.htm
(defn levenshtein
  "Uses a matrix to compute the levenshtein distance of two sequence"
  [a b]
  (let [n (count a) m (count b) cell (fn [m i j] (nth (nth m i) j))]
    (if (some zero? (list n m))
      (max n m)
      (loop [matrix (into
                     [(into [] (range 0 (inc n)))]
                     (for [j (range 1 (inc m))]
                       (into [j] (repeat n 0))))
             indeces (for [j (range 1 (inc n))
                           i (range 1 (inc m))]
                       (list i j))]
        (if (seq indeces) 
          (let [i (ffirst indeces)
                j (second (first indeces))
                new-cell (min
                          (inc (cell matrix (dec i) j))
                          (inc (cell matrix i (dec j)))
                          (+ (cell matrix (dec i) (dec j))
                             (if (= (nth a (dec j)) (nth b (dec i))) 0 1)))
                matrix' (assoc matrix i (assoc (nth matrix i) j new-cell))]
            (recur matrix' (rest indeces)))
          (last (last matrix)))))))

(defn into-camel-case
  [string]
  (apply str (reduce
              (fn [a b]
                (concat a (conj (rest b) (Character/toUpperCase (first b)))))
              (map #(remove #{\-} %) (re-seq #"\w+-|\w+" string)))))

(defn k-combinations
  [k s]
  (loop [sets (map hash-set s)]
    (if (every? #{k} (map count sets))
      (set sets)
      (recur (for [x sets y s
                   :when (not (x y))]
               (conj x y))))))

(defn to-roman
  [i]
  (let [val-map (sorted-map 1000 "M" 500 "D" 100 "C" 50 "L" 10 "X" 5 "V" 1 "I"
                            900 "CM" 400 "CD" 90 "XC" 40 "XL" 9 "IX" 4 "IV")
        result (first (drop-while #(> % i) ((comp reverse keys) val-map)))]
    (if result
      (str (val-map result) (to-roman (- i result))))))

(defn v-to-map
  [v]
  (reduce
   #(if (keyword? %2)
      (assoc %1 %2 [])
      (assoc %1 (first (last %1)) (conj (second (last %1)) %2)))
   (cons (sorted-map) v)))

(defn number-maze
  [a b]
  (letfn [(queue-fn [i n]
            (vector n (* 2 n) (/ n 2) (+ 2 n) (inc i)))]
    (loop [queue (vector (queue-fn 0 a))]
      (let [current (first queue)]
        (if (= b (current 0))
          (current 4)
          (recur (into (subvec queue 1)
                       (map
                        (partial queue-fn (current 4))
                        (sort (remove ratio? (subvec current 1 4)))))))))))

"Returns an fn which computes x^n"
(defn simple-closure
  [x]
  (fn [n] (nth (iterate (partial * n) 1) x)))

"Lazily searches all the colls for the smallest number appearing in all of them"
(defn lazy-search
  [coll & colls]
  (letfn [(search [sets remaining-colls]
            (if-let [result (first (apply clojure.set/intersection sets))]
              result
              (recur (map #(conj %1 (first %2)) sets remaining-colls)
                     (map #(drop-while
                            (partial > (apply max (map first remaining-colls))) %)
                            remaining-colls))))]
    (search (map #(hash-set (first %)) (cons coll colls)) (cons coll colls))))

(defn pronounciations
  [v]
  (lazy-seq
   (let [current (into [] (mapcat #(list (count %) (first %)) (partition-by identity v)))]
     (cons current (pronounciations current)))))

(defn cross-word-puzzle
  [word puzzle]
  (let [index-sets
        (loop [acc (hash-set #{}) added acc]
          (if-let [to-add
                   (seq (for [subset added 
                              e (range 0 (count word))
                              :when (not (subset e))]
                          (conj subset e)))]
            (recur (into acc to-add) (set to-add))
            (into acc added)))
        blanks
        (->>
         (remove (hash-set (set (range 0 (count word))) #{}) index-sets)
         (map #(interleave % (repeat \_)))
         (map #(apply (partial assoc (into [] word)) %)))
        h (map (partial remove #{\space}) puzzle)
        v (for [i (range 0 (count (first h)))] (map #(nth % i) h))]
    ((complement nil?)
     (some (set blanks) (mapcat #(partition-by (partial = \#) %) (concat v h))))))

(defn sequs-horriblis
  [n coll]
  (letfn [(conj-not-empty [coll x] (if (seq x) (conj coll x) coll))]
   ((fn f [remaining-n new-coll old-coll]
     (let [e (first old-coll)
           remaining-n' (if (number? e) (- remaining-n e) remaining-n)
           old-coll' (rest old-coll)]
       (cond (or (empty? old-coll) (> 0 remaining-n')) new-coll
             (coll? e) (f (apply (partial - remaining-n') (flatten e))
                          (conj-not-empty new-coll (f remaining-n' [] e))
                          old-coll')
             :else (f remaining-n' (conj new-coll e) old-coll')))) n [] coll)))

(defn data-dance
  [& args]
    (reify
      Object
      (toString [this]
        (let [sorted (sort < args)]
          (str (apply str (interleave (drop-last sorted) (repeat ", ")))
               (last sorted))))
      clojure.lang.Seqable
      (seq [this]
        (loop [seen (hash-set) built (list) rem-coll args]
          (cond (empty? rem-coll) (seq (reverse built))
                (seen (first rem-coll)) (recur seen built (rest rem-coll))
                :else (recur (conj seen (first rem-coll))
                             (conj built (first rem-coll))
                             (rest rem-coll)))))))
