{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module CPF_2_to_3(Char, Xml, Mapping, Xmldoc, Sum, cpf_2_to_3_phase_1) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

newtype Char = Chr Integer;

data Xml = XML [Char] [([Char], [Char])] [Xml] | XML_text [Char];

integer_of_char :: Char -> Integer;
integer_of_char (Chr x) = x;

equal_char :: Char -> Char -> Bool;
equal_char c d = integer_of_char c == integer_of_char d;

instance Eq Char where {
  a == b = equal_char a b;
};

instance Eq Xml where {
  a == b = equal_xml a b;
};

equal_xml :: Xml -> Xml -> Bool;
equal_xml (XML x11 x12 x13) (XML_text x2) = False;
equal_xml (XML_text x2) (XML x11 x12 x13) = False;
equal_xml (XML_text x2) (XML_text y2) = x2 == y2;
equal_xml (XML x11 x12 x13) (XML y11 y12 y13) =
  x11 == y11 && x12 == y12 && x13 == y13;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

data Ordera = Eqa | Lt | Gt;

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

class (Order a) => Linorder a where {
};

comparator_of :: forall a. (Eq a, Linorder a) => a -> a -> Ordera;
comparator_of x y = (if less x y then Lt else (if x == y then Eqa else Gt));

comparator_prod ::
  forall a b.
    (a -> a -> Ordera) -> (b -> b -> Ordera) -> (a, b) -> (a, b) -> Ordera;
comparator_prod comp_a comp_b (x, xa) (y, ya) = (case comp_a x y of {
          Eqa -> comp_b xa ya;
          Lt -> Lt;
          Gt -> Gt;
        });

comparator_list :: forall a. (a -> a -> Ordera) -> [a] -> [a] -> Ordera;
comparator_list comp_a (x : xa) (y : ya) =
  (case comp_a x y of {
    Eqa -> comparator_list comp_a xa ya;
    Lt -> Lt;
    Gt -> Gt;
  });
comparator_list comp_a (x : xa) [] = Gt;
comparator_list comp_a [] (y : ya) = Lt;
comparator_list comp_a [] [] = Eqa;

less_eq_char :: Char -> Char -> Bool;
less_eq_char c d = integer_of_char c <= integer_of_char d;

less_char :: Char -> Char -> Bool;
less_char c d = integer_of_char c < integer_of_char d;

instance Ord Char where {
  less_eq = less_eq_char;
  less = less_char;
};

instance Preorder Char where {
};

instance Order Char where {
};

instance Linorder Char where {
};

comparator_xml :: Xml -> Xml -> Ordera;
comparator_xml (XML_text x) (XML_text yc) = comparator_list comparator_of x yc;
comparator_xml (XML_text x) (XML y ya yb) = Gt;
comparator_xml (XML x xa xb) (XML_text yc) = Lt;
comparator_xml (XML x xa xb) (XML y ya yb) =
  (case comparator_list comparator_of x y of {
    Eqa ->
      (case comparator_list
              (comparator_prod (comparator_list comparator_of)
                (comparator_list comparator_of))
              xa ya
        of {
        Eqa -> comparator_list comparator_xml xb yb;
        Lt -> Lt;
        Gt -> Gt;
      });
    Lt -> Lt;
    Gt -> Gt;
  });

compare_xml :: Xml -> Xml -> Ordera;
compare_xml = comparator_xml;

le_of_comp :: forall a. (a -> a -> Ordera) -> a -> a -> Bool;
le_of_comp acomp x y = (case acomp x y of {
                         Eqa -> True;
                         Lt -> True;
                         Gt -> False;
                       });

less_eq_xml :: Xml -> Xml -> Bool;
less_eq_xml = le_of_comp compare_xml;

lt_of_comp :: forall a. (a -> a -> Ordera) -> a -> a -> Bool;
lt_of_comp acomp x y = (case acomp x y of {
                         Eqa -> False;
                         Lt -> True;
                         Gt -> False;
                       });

less_xml :: Xml -> Xml -> Bool;
less_xml = lt_of_comp compare_xml;

instance Ord Xml where {
  less_eq = less_eq_xml;
  less = less_xml;
};

instance Preorder Xml where {
};

instance Order Xml where {
};

instance Linorder Xml where {
};

less_eq_list :: forall a. (Eq a, Order a) => [a] -> [a] -> Bool;
less_eq_list (x : xs) (y : ys) = less x y || x == y && less_eq_list xs ys;
less_eq_list [] xs = True;
less_eq_list (x : xs) [] = False;

less_list :: forall a. (Eq a, Order a) => [a] -> [a] -> Bool;
less_list (x : xs) (y : ys) = less x y || x == y && less_list xs ys;
less_list [] (x : xs) = True;
less_list xs [] = False;

instance (Eq a, Order a) => Ord [a] where {
  less_eq = less_eq_list;
  less = less_list;
};

instance (Eq a, Order a) => Preorder [a] where {
};

instance (Eq a, Order a) => Order [a] where {
};

instance (Eq a, Linorder a) => Linorder [a] where {
};

newtype Nat = Nat Integer;

shows_prec_char :: Nat -> Char -> [Char] -> [Char];
shows_prec_char p c = (\ a -> c : a);

shows_string :: [Char] -> [Char] -> [Char];
shows_string = (\ a b -> a ++ b);

shows_list_char :: [Char] -> [Char] -> [Char];
shows_list_char cs = shows_string cs;

class Showa a where {
  shows_prec :: Nat -> a -> [Char] -> [Char];
  shows_list :: [a] -> [Char] -> [Char];
};

instance Showa Char where {
  shows_prec = shows_prec_char;
  shows_list = shows_list_char;
};

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

data Num = One | Bit0 Num | Bit1 Num;

data Color = R | B;

data Rbta a b = Empty | Branch Color (Rbta a b) a b (Rbta a b);

newtype Rbt b a = RBT (Rbta b a);

newtype Mapping a b = Mapping (Rbt a b);

newtype Set a = Setm (Mapping a ());

data Xmldoc = XMLDOC [[Char]] Xml;

data Sum a b = Inl a | Inr b;

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

tag :: Xml -> [Char];
tag (XML name uu uv) = name;
tag (XML_text uw) = [];

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

drop :: forall a. Nat -> [a] -> [a];
drop n [] = [];
drop n (x : xs) =
  (if equal_nat n zero_nat then x : xs else drop (minus_nat n one_nat) xs);

last :: forall a. [a] -> a;
last (x : xs) = (if null xs then x else last xs);

take :: forall a. Nat -> [a] -> [a];
take n [] = [];
take n (x : xs) =
  (if equal_nat n zero_nat then [] else x : take (minus_nat n one_nat) xs);

empty :: forall a b. (Linorder a) => Rbt a b;
empty = RBT Empty;

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

balance :: forall a b. Rbta a b -> a -> b -> Rbta a b -> Rbta a b;
balance (Branch R a w x b) s t (Branch R c y z d) =
  Branch R (Branch B a w x b) s t (Branch B c y z d);
balance (Branch R (Branch R a w x b) s t c) y z Empty =
  Branch R (Branch B a w x b) s t (Branch B c y z Empty);
balance (Branch R (Branch R a w x b) s t c) y z (Branch B va vb vc vd) =
  Branch R (Branch B a w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch R Empty w x (Branch R b s t c)) y z Empty =
  Branch R (Branch B Empty w x b) s t (Branch B c y z Empty);
balance (Branch R (Branch B va vb vc vd) w x (Branch R b s t c)) y z Empty =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z Empty);
balance (Branch R Empty w x (Branch R b s t c)) y z (Branch B va vb vc vd) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch R (Branch B ve vf vg vh) w x (Branch R b s t c)) y z
  (Branch B va vb vc vd) =
  Branch R (Branch B (Branch B ve vf vg vh) w x b) s t
    (Branch B c y z (Branch B va vb vc vd));
balance Empty w x (Branch R b s t (Branch R c y z d)) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z d);
balance (Branch B va vb vc vd) w x (Branch R b s t (Branch R c y z d)) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z d);
balance Empty w x (Branch R (Branch R b s t c) y z Empty) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z Empty);
balance Empty w x (Branch R (Branch R b s t c) y z (Branch B va vb vc vd)) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch B va vb vc vd) w x (Branch R (Branch R b s t c) y z Empty) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z Empty);
balance (Branch B va vb vc vd) w x
  (Branch R (Branch R b s t c) y z (Branch B ve vf vg vh)) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t
    (Branch B c y z (Branch B ve vf vg vh));
balance Empty s t Empty = Branch B Empty s t Empty;
balance Empty s t (Branch B va vb vc vd) =
  Branch B Empty s t (Branch B va vb vc vd);
balance Empty s t (Branch v Empty vb vc Empty) =
  Branch B Empty s t (Branch v Empty vb vc Empty);
balance Empty s t (Branch v (Branch B ve vf vg vh) vb vc Empty) =
  Branch B Empty s t (Branch v (Branch B ve vf vg vh) vb vc Empty);
balance Empty s t (Branch v Empty vb vc (Branch B vf vg vh vi)) =
  Branch B Empty s t (Branch v Empty vb vc (Branch B vf vg vh vi));
balance Empty s t (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi))
  = Branch B Empty s t
      (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi));
balance (Branch B va vb vc vd) s t Empty =
  Branch B (Branch B va vb vc vd) s t Empty;
balance (Branch B va vb vc vd) s t (Branch B ve vf vg vh) =
  Branch B (Branch B va vb vc vd) s t (Branch B ve vf vg vh);
balance (Branch B va vb vc vd) s t (Branch v Empty vf vg Empty) =
  Branch B (Branch B va vb vc vd) s t (Branch v Empty vf vg Empty);
balance (Branch B va vb vc vd) s t (Branch v (Branch B vi vj vk vl) vf vg Empty)
  = Branch B (Branch B va vb vc vd) s t
      (Branch v (Branch B vi vj vk vl) vf vg Empty);
balance (Branch B va vb vc vd) s t (Branch v Empty vf vg (Branch B vj vk vl vm))
  = Branch B (Branch B va vb vc vd) s t
      (Branch v Empty vf vg (Branch B vj vk vl vm));
balance (Branch B va vb vc vd) s t
  (Branch v (Branch B vi vn vo vp) vf vg (Branch B vj vk vl vm)) =
  Branch B (Branch B va vb vc vd) s t
    (Branch v (Branch B vi vn vo vp) vf vg (Branch B vj vk vl vm));
balance (Branch v Empty vb vc Empty) s t Empty =
  Branch B (Branch v Empty vb vc Empty) s t Empty;
balance (Branch v Empty vb vc (Branch B ve vf vg vh)) s t Empty =
  Branch B (Branch v Empty vb vc (Branch B ve vf vg vh)) s t Empty;
balance (Branch v (Branch B vf vg vh vi) vb vc Empty) s t Empty =
  Branch B (Branch v (Branch B vf vg vh vi) vb vc Empty) s t Empty;
balance (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) s t Empty
  = Branch B (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) s t
      Empty;
balance (Branch v Empty vf vg Empty) s t (Branch B va vb vc vd) =
  Branch B (Branch v Empty vf vg Empty) s t (Branch B va vb vc vd);
balance (Branch v Empty vf vg (Branch B vi vj vk vl)) s t (Branch B va vb vc vd)
  = Branch B (Branch v Empty vf vg (Branch B vi vj vk vl)) s t
      (Branch B va vb vc vd);
balance (Branch v (Branch B vj vk vl vm) vf vg Empty) s t (Branch B va vb vc vd)
  = Branch B (Branch v (Branch B vj vk vl vm) vf vg Empty) s t
      (Branch B va vb vc vd);
balance (Branch v (Branch B vj vk vl vm) vf vg (Branch B vi vn vo vp)) s t
  (Branch B va vb vc vd) =
  Branch B (Branch v (Branch B vj vk vl vm) vf vg (Branch B vi vn vo vp)) s t
    (Branch B va vb vc vd);

rbt_ins ::
  forall a b. (Ord a) => (a -> b -> b -> b) -> a -> b -> Rbta a b -> Rbta a b;
rbt_ins f k v Empty = Branch R Empty k v Empty;
rbt_ins f k v (Branch B l x y r) =
  (if less k x then balance (rbt_ins f k v l) x y r
    else (if less x k then balance l x y (rbt_ins f k v r)
           else Branch B l x (f k y v) r));
rbt_ins f k v (Branch R l x y r) =
  (if less k x then Branch R (rbt_ins f k v l) x y r
    else (if less x k then Branch R l x y (rbt_ins f k v r)
           else Branch R l x (f k y v) r));

paint :: forall a b. Color -> Rbta a b -> Rbta a b;
paint c Empty = Empty;
paint c (Branch uu l k v r) = Branch c l k v r;

rbt_insert_with_key ::
  forall a b. (Ord a) => (a -> b -> b -> b) -> a -> b -> Rbta a b -> Rbta a b;
rbt_insert_with_key f k v t = paint B (rbt_ins f k v t);

rbt_insert :: forall a b. (Ord a) => a -> b -> Rbta a b -> Rbta a b;
rbt_insert = rbt_insert_with_key (\ _ _ nv -> nv);

impl_of :: forall b a. (Linorder b) => Rbt b a -> Rbta b a;
impl_of (RBT x) = x;

insert :: forall a b. (Linorder a) => a -> b -> Rbt a b -> Rbt a b;
insert xc xd xe = RBT (rbt_insert xc xd (impl_of xe));

rbt_lookup :: forall a b. (Ord a) => Rbta a b -> a -> Maybe b;
rbt_lookup Empty k = Nothing;
rbt_lookup (Branch uu l x y r) k =
  (if less k x then rbt_lookup l k
    else (if less x k then rbt_lookup r k else Just y));

lookup :: forall a b. (Linorder a) => Rbt a b -> a -> Maybe b;
lookup x = rbt_lookup (impl_of x);

update :: forall a b. (Linorder a) => a -> b -> Mapping a b -> Mapping a b;
update k v (Mapping t) = Mapping (insert k v t);

inserta :: forall a. (Linorder a) => a -> Set a -> Set a;
inserta x (Setm m) = Setm (update x () m);

lookupa :: forall a b. (Linorder a) => Mapping a b -> a -> Maybe b;
lookupa (Mapping t) = lookup t;

member :: forall a. (Linorder a) => a -> Set a -> Bool;
member x (Setm m) = (case lookupa m x of {
                      Nothing -> False;
                      Just _ -> True;
                    });

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

char_0x7A :: Char;
char_0x7A = Chr (122 :: Integer);

char_0x79 :: Char;
char_0x79 = Chr (121 :: Integer);

char_0x78 :: Char;
char_0x78 = Chr (120 :: Integer);

char_0x77 :: Char;
char_0x77 = Chr (119 :: Integer);

char_0x76 :: Char;
char_0x76 = Chr (118 :: Integer);

char_0x75 :: Char;
char_0x75 = Chr (117 :: Integer);

char_0x74 :: Char;
char_0x74 = Chr (116 :: Integer);

char_0x73 :: Char;
char_0x73 = Chr (115 :: Integer);

char_0x72 :: Char;
char_0x72 = Chr (114 :: Integer);

char_0x71 :: Char;
char_0x71 = Chr (113 :: Integer);

char_0x70 :: Char;
char_0x70 = Chr (112 :: Integer);

char_0x6F :: Char;
char_0x6F = Chr (111 :: Integer);

char_0x6E :: Char;
char_0x6E = Chr (110 :: Integer);

char_0x6D :: Char;
char_0x6D = Chr (109 :: Integer);

char_0x6C :: Char;
char_0x6C = Chr (108 :: Integer);

char_0x6B :: Char;
char_0x6B = Chr (107 :: Integer);

char_0x6A :: Char;
char_0x6A = Chr (106 :: Integer);

char_0x69 :: Char;
char_0x69 = Chr (105 :: Integer);

char_0x68 :: Char;
char_0x68 = Chr (104 :: Integer);

char_0x67 :: Char;
char_0x67 = Chr (103 :: Integer);

char_0x66 :: Char;
char_0x66 = Chr (102 :: Integer);

char_0x65 :: Char;
char_0x65 = Chr (101 :: Integer);

char_0x64 :: Char;
char_0x64 = Chr (100 :: Integer);

char_0x63 :: Char;
char_0x63 = Chr (99 :: Integer);

char_0x62 :: Char;
char_0x62 = Chr (98 :: Integer);

char_0x61 :: Char;
char_0x61 = Chr (97 :: Integer);

char_0x5F :: Char;
char_0x5F = Chr (95 :: Integer);

char_0x5A :: Char;
char_0x5A = Chr (90 :: Integer);

char_0x59 :: Char;
char_0x59 = Chr (89 :: Integer);

char_0x58 :: Char;
char_0x58 = Chr (88 :: Integer);

char_0x57 :: Char;
char_0x57 = Chr (87 :: Integer);

char_0x56 :: Char;
char_0x56 = Chr (86 :: Integer);

char_0x55 :: Char;
char_0x55 = Chr (85 :: Integer);

char_0x54 :: Char;
char_0x54 = Chr (84 :: Integer);

char_0x53 :: Char;
char_0x53 = Chr (83 :: Integer);

char_0x52 :: Char;
char_0x52 = Chr (82 :: Integer);

char_0x51 :: Char;
char_0x51 = Chr (81 :: Integer);

char_0x50 :: Char;
char_0x50 = Chr (80 :: Integer);

char_0x4F :: Char;
char_0x4F = Chr (79 :: Integer);

char_0x4E :: Char;
char_0x4E = Chr (78 :: Integer);

char_0x4D :: Char;
char_0x4D = Chr (77 :: Integer);

char_0x4C :: Char;
char_0x4C = Chr (76 :: Integer);

char_0x4B :: Char;
char_0x4B = Chr (75 :: Integer);

char_0x4A :: Char;
char_0x4A = Chr (74 :: Integer);

char_0x49 :: Char;
char_0x49 = Chr (73 :: Integer);

char_0x48 :: Char;
char_0x48 = Chr (72 :: Integer);

char_0x47 :: Char;
char_0x47 = Chr (71 :: Integer);

char_0x46 :: Char;
char_0x46 = Chr (70 :: Integer);

char_0x45 :: Char;
char_0x45 = Chr (69 :: Integer);

char_0x44 :: Char;
char_0x44 = Chr (68 :: Integer);

char_0x43 :: Char;
char_0x43 = Chr (67 :: Integer);

char_0x42 :: Char;
char_0x42 = Chr (66 :: Integer);

char_0x41 :: Char;
char_0x41 = Chr (65 :: Integer);

char_0x3B :: Char;
char_0x3B = Chr (59 :: Integer);

char_0x3A :: Char;
char_0x3A = Chr (58 :: Integer);

char_0x39 :: Char;
char_0x39 = Chr (57 :: Integer);

char_0x38 :: Char;
char_0x38 = Chr (56 :: Integer);

char_0x37 :: Char;
char_0x37 = Chr (55 :: Integer);

char_0x36 :: Char;
char_0x36 = Chr (54 :: Integer);

char_0x35 :: Char;
char_0x35 = Chr (53 :: Integer);

char_0x34 :: Char;
char_0x34 = Chr (52 :: Integer);

char_0x33 :: Char;
char_0x33 = Chr (51 :: Integer);

char_0x32 :: Char;
char_0x32 = Chr (50 :: Integer);

char_0x31 :: Char;
char_0x31 = Chr (49 :: Integer);

char_0x30 :: Char;
char_0x30 = Chr (48 :: Integer);

char_0x2D :: Char;
char_0x2D = Chr (45 :: Integer);

char_0x26 :: Char;
char_0x26 = Chr (38 :: Integer);

letters :: [Char];
letters =
  [char_0x61, char_0x62, char_0x63, char_0x64, char_0x65, char_0x66, char_0x67,
    char_0x68, char_0x69, char_0x6A, char_0x6B, char_0x6C, char_0x6D, char_0x6E,
    char_0x6F, char_0x70, char_0x71, char_0x72, char_0x73, char_0x74, char_0x75,
    char_0x76, char_0x77, char_0x78, char_0x79, char_0x7A, char_0x41, char_0x42,
    char_0x43, char_0x44, char_0x45, char_0x46, char_0x47, char_0x48, char_0x49,
    char_0x4A, char_0x4B, char_0x4C, char_0x4D, char_0x4E, char_0x4F, char_0x50,
    char_0x51, char_0x52, char_0x53, char_0x54, char_0x55, char_0x56, char_0x57,
    char_0x58, char_0x59, char_0x5A, char_0x5F, char_0x30, char_0x31, char_0x32,
    char_0x33, char_0x34, char_0x35, char_0x36, char_0x37, char_0x38, char_0x39,
    char_0x26, char_0x3B, char_0x3A, char_0x2D];

hd :: forall a. [a] -> a;
hd (x21 : x22) = x21;

tl :: forall a. [a] -> [a];
tl [] = [];
tl (x21 : x22) = x22;

rbt_bulkload :: forall a b. (Ord a) => [(a, b)] -> Rbta a b;
rbt_bulkload xs = foldr (\ (a, b) -> rbt_insert a b) xs Empty;

bulkload :: forall a b. (Linorder a) => [(a, b)] -> Rbt a b;
bulkload xa = RBT (rbt_bulkload xa);

children :: Xml -> [Xml];
children (XML uu uv cs) = cs;
children (XML_text uw) = [];

tabulate :: forall a b. (Linorder a) => [a] -> (a -> b) -> Mapping a b;
tabulate ks f = Mapping (bulkload (map (\ k -> (k, f k)) ks));

set :: forall a. (Linorder a) => [a] -> Set a;
set xs = Setm (tabulate xs (\ _ -> ()));

emptya :: forall a b. (Linorder a) => Mapping a b;
emptya = Mapping empty;

is_letter :: Char -> Bool;
is_letter c =
  let {
    ci = integer_of_char c;
  } in (97 :: Integer) <= ci && ci <= (122 :: Integer) ||
         ((65 :: Integer) <= ci && ci <= (90 :: Integer) ||
           ((48 :: Integer) <= ci && ci <= (59 :: Integer) ||
             (ci == (95 :: Integer) ||
               (ci == (38 :: Integer) || ci == (45 :: Integer)))));

update_tokens :: forall a. ([a] -> [a]) -> [a] -> Sum [Char] ([a], [a]);
update_tokens f ts = Inr (ts, f ts);

char_0x3C :: Char;
char_0x3C = Chr (60 :: Integer);

char_0x21 :: Char;
char_0x21 = Chr (33 :: Integer);

comment_error :: forall a. [a];
comment_error =
  (error :: forall a. String -> (() -> a) -> a) "comment not terminated"
    (\ _ -> []);

comment_error_hyphen :: forall a. [a];
comment_error_hyphen =
  (error :: forall a. String -> (() -> a) -> a) "double hyphen within comment"
    (\ _ -> []);

rc_open_1 :: [Char] -> [Char];
rc_open_1 [] = [];
rc_open_1 (c : cs) =
  (if integer_of_char c == (60 :: Integer) then rc_open_2 cs
    else c : rc_open_1 cs);

rc_close_3 :: [Char] -> [Char];
rc_close_3 [] = comment_error;
rc_close_3 (c : cs) =
  (if integer_of_char c == (62 :: Integer) then rc_open_1 cs
    else comment_error_hyphen);

rc_close_2 :: [Char] -> [Char];
rc_close_2 [] = comment_error;
rc_close_2 (c : cs) =
  (if integer_of_char c == (45 :: Integer) then rc_close_3 cs
    else rc_close_1 cs);

rc_close_1 :: [Char] -> [Char];
rc_close_1 [] = comment_error;
rc_close_1 (c : cs) =
  (if integer_of_char c == (45 :: Integer) then rc_close_2 cs
    else rc_close_1 cs);

rc_open_4 :: [Char] -> [Char];
rc_open_4 [] = [char_0x3C, char_0x21, char_0x2D];
rc_open_4 (c : cs) =
  let {
    ic = integer_of_char c;
  } in (if ic == (45 :: Integer) then rc_close_1 cs
         else (if ic == (60 :: Integer)
                then c : char_0x21 : char_0x2D : rc_open_2 cs
                else char_0x3C : char_0x21 : char_0x2D : c : rc_open_1 cs));

rc_open_3 :: [Char] -> [Char];
rc_open_3 [] = [char_0x3C, char_0x21];
rc_open_3 (c : cs) =
  let {
    ic = integer_of_char c;
  } in (if ic == (45 :: Integer) then rc_open_4 cs
         else (if ic == (60 :: Integer) then c : char_0x21 : rc_open_2 cs
                else char_0x3C : char_0x21 : c : rc_open_1 cs));

rc_open_2 :: [Char] -> [Char];
rc_open_2 [] = [char_0x3C];
rc_open_2 (c : cs) =
  let {
    ic = integer_of_char c;
  } in (if ic == (33 :: Integer) then rc_open_3 cs
         else (if ic == (60 :: Integer) then c : rc_open_2 cs
                else char_0x3C : c : rc_open_1 cs));

remove_comments :: [Char] -> [Char];
remove_comments xs = rc_open_1 xs;

returna :: forall a b. a -> [b] -> Sum [Char] (a, [b]);
returna x = (\ ts -> Inr (x, ts));

bind :: forall a b c. Sum a b -> (b -> Sum a c) -> Sum a c;
bind m f = (case m of {
             Inl a -> Inl a;
             Inr a -> f a;
           });

binda ::
  forall a b c.
    ([a] -> Sum [Char] (b, [a])) ->
      (b -> [a] -> Sum [Char] (c, [a])) -> [a] -> Sum [Char] (c, [a]);
binda m f ts = bind (m ts) (\ (a, b) -> f a b);

char_0x3F :: Char;
char_0x3F = Chr (63 :: Integer);

char_0x3E :: Char;
char_0x3E = Chr (62 :: Integer);

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (max (0 :: Integer) k);

shows_prec_list :: forall a. (Showa a) => Nat -> [a] -> [Char] -> [Char];
shows_prec_list p xs = shows_list xs;

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (suc n) xs;
gen_length n [] = n;

size_list :: forall a. [a] -> Nat;
size_list = gen_length zero_nat;

char_0x20 :: Char;
char_0x20 = Chr (32 :: Integer);

char_0x27 :: Char;
char_0x27 = Chr (39 :: Integer);

shows_quote :: ([Char] -> [Char]) -> [Char] -> [Char];
shows_quote s =
  (shows_prec_char zero_nat char_0x27 . s) . shows_prec_char zero_nat char_0x27;

scan_upto :: [Char] -> [Char] -> Sum [Char] ([Char], [Char]);
scan_upto end (t : ts) =
  (if map snd (zip end (t : ts)) == end
    then Inr (end, drop (size_list end) (t : ts))
    else bind (scan_upto end ts) (\ (res, tsa) -> Inr (t : res, tsa)));
scan_upto end [] =
  Inl ([char_0x64, char_0x69, char_0x64, char_0x20, char_0x6E, char_0x6F,
         char_0x74, char_0x20, char_0x66, char_0x69, char_0x6E, char_0x64,
         char_0x20, char_0x65, char_0x6E, char_0x64, char_0x2D, char_0x6D,
         char_0x61, char_0x72, char_0x6B, char_0x65, char_0x72, char_0x20] ++
        shows_quote (shows_prec_list zero_nat end) []);

trim :: [Char] -> [Char];
trim =
  dropWhile
    (\ c ->
      let {
        ci = integer_of_char c;
      } in (if (34 :: Integer) <= ci then False
             else ci == (32 :: Integer) ||
                    (ci == (10 :: Integer) ||
                      (ci == (9 :: Integer) || ci == (13 :: Integer)))));

spaces :: [Char] -> Sum [Char] ((), [Char]);
spaces cs = Inr ((), trim cs);

parse_header :: [Char] -> Sum [Char] ([[Char]], [Char]);
parse_header ts =
  (if take (nat_of_integer (2 :: Integer)) (trim ts) == [char_0x3C, char_0x3F]
    then binda (scan_upto [char_0x3F, char_0x3E])
           (\ h -> binda parse_header (\ hs -> returna (h : hs))) ts
    else binda spaces (\ _ -> returna []) ts);

char_0x2C :: Char;
char_0x2C = Chr (44 :: Integer);

err_expecting :: forall a b. (Showa a) => [Char] -> [a] -> Sum [Char] (b, [a]);
err_expecting msg ts =
  Inl ([char_0x65, char_0x78, char_0x70, char_0x65, char_0x63, char_0x74,
         char_0x69, char_0x6E, char_0x67, char_0x20] ++
        msg ++
          [char_0x2C, char_0x20, char_0x62, char_0x75, char_0x74, char_0x20,
            char_0x66, char_0x6F, char_0x75, char_0x6E, char_0x64, char_0x3A,
            char_0x20] ++
            shows_quote
              (shows_prec_list zero_nat
                (take (nat_of_integer (30 :: Integer)) ts))
              []);

eoi :: forall a. (Showa a) => [a] -> Sum [Char] ((), [a]);
eoi [] = Inr ((), []);
eoi (v : va) =
  err_expecting
    [char_0x65, char_0x6E, char_0x64, char_0x20, char_0x6F, char_0x66,
      char_0x20, char_0x69, char_0x6E, char_0x70, char_0x75, char_0x74]
    (v : va);

char_0x2F :: Char;
char_0x2F = Chr (47 :: Integer);

char_0x3D :: Char;
char_0x3D = Chr (61 :: Integer);

char_0x22 :: Char;
char_0x22 = Chr (34 :: Integer);

exactly_aux ::
  [Char] -> [Char] -> [Char] -> [Char] -> Sum [Char] ([Char], [Char]);
exactly_aux s i (x : xs) (y : ys) =
  (if equal_char x y then exactly_aux s i xs ys
    else err_expecting ([char_0x22] ++ s ++ [char_0x22]) i);
exactly_aux s i [] xs = Inr (s, trim xs);
exactly_aux s i (x : xs) [] = err_expecting ([char_0x22] ++ s ++ [char_0x22]) i;

exactly :: [Char] -> [Char] -> Sum [Char] ([Char], [Char]);
exactly s x = exactly_aux s x s x;

many :: (Char -> Bool) -> [Char] -> Sum [Char] ([Char], [Char]);
many p (t : ts) =
  (if p t then bind (many p ts) (\ (rs, tsa) -> Inr (t : rs, tsa))
    else Inr ([], t : ts));
many p [] = Inr ([], []);

parse_attribute_value :: [Char] -> Sum [Char] ([Char], [Char]);
parse_attribute_value =
  binda (exactly [char_0x22])
    (\ _ ->
      binda (many (\ y -> not (equal_char char_0x22 y)))
        (\ v -> binda (exactly [char_0x22]) (\ _ -> returna v)));

many_letters_main :: [Char] -> ([Char], [Char]);
many_letters_main [] = ([], []);
many_letters_main (c : cs) =
  (if is_letter c then (case many_letters_main cs of {
                         (ds, a) -> (c : ds, a);
                       })
    else ([], c : cs));

parse_name :: [Char] -> Sum [Char] ([Char], [Char]);
parse_name s =
  (case many_letters_main s of {
    (n, ts) ->
      (if null n
        then Inl ([char_0x65, char_0x78, char_0x70, char_0x65, char_0x63,
                    char_0x74, char_0x65, char_0x64, char_0x20, char_0x6C,
                    char_0x65, char_0x74, char_0x74, char_0x65, char_0x72,
                    char_0x20] ++
                   letters ++
                     [char_0x20, char_0x62, char_0x75, char_0x74, char_0x20,
                       char_0x66, char_0x69, char_0x72, char_0x73, char_0x74,
                       char_0x20, char_0x73, char_0x79, char_0x6D, char_0x62,
                       char_0x6F, char_0x6C, char_0x20, char_0x69, char_0x73,
                       char_0x20, char_0x22] ++
                       take one_nat s ++ [char_0x22])
        else Inr (n, trim ts));
  });

parse_attributes :: [Char] -> Sum [Char] ([([Char], [Char])], [Char]);
parse_attributes (c : s) =
  let {
    ic = integer_of_char c;
  } in (if ic == (47 :: Integer) || ic == (62 :: Integer) then Inr ([], c : s)
         else binda parse_name
                (\ k ->
                  binda (exactly [char_0x3D])
                    (\ _ ->
                      binda parse_attribute_value
                        (\ v ->
                          binda parse_attributes
                            (\ atts -> returna ((k, v) : atts)))))
                (c : s));
parse_attributes [] = Inr ([], []);

char_0x5D :: Char;
char_0x5D = Chr (93 :: Integer);

char_0x5B :: Char;
char_0x5B = Chr (91 :: Integer);

oneof_closed :: [Char] -> Sum [Char] ([Char], [Char]);
oneof_closed (x : xs) =
  (if equal_char x char_0x3E then Inr ([char_0x3E], trim xs)
    else (if equal_char x char_0x2F && (case xs of {
 [] -> False;
 y : _ -> equal_char y char_0x3E;
                                       })
           then Inr ([char_0x2F, char_0x3E], trim (tl xs))
           else err_expecting
                  [char_0x6F, char_0x6E, char_0x65, char_0x20, char_0x6F,
                    char_0x66, char_0x20, char_0x5B, char_0x2F, char_0x3E,
                    char_0x2C, char_0x20, char_0x3E, char_0x5D]
                  (x : xs)));
oneof_closed [] =
  err_expecting
    [char_0x6F, char_0x6E, char_0x65, char_0x20, char_0x6F, char_0x66,
      char_0x20, char_0x5B, char_0x2F, char_0x3E, char_0x2C, char_0x20,
      char_0x3E, char_0x5D]
    [];

oneof_closed_combined ::
  forall a.
    ([Char] -> Sum [Char] (a, [Char])) ->
      ([Char] -> Sum [Char] (a, [Char])) -> [Char] -> Sum [Char] (a, [Char]);
oneof_closed_combined p q (x : xs) =
  let {
    xi = integer_of_char x;
  } in (if xi == (62 :: Integer) then q (trim xs)
         else (if xi == (47 :: Integer)
                then (case xs of {
                       [] -> err_expecting
                               [char_0x6F, char_0x6E, char_0x65, char_0x20,
                                 char_0x6F, char_0x66, char_0x20, char_0x5B,
                                 char_0x2F, char_0x3E, char_0x2C, char_0x20,
                                 char_0x3E, char_0x5D]
                               (x : xs);
                       y : ys ->
                         (if integer_of_char y == (62 :: Integer)
                           then p (trim ys)
                           else err_expecting
                                  [char_0x6F, char_0x6E, char_0x65, char_0x20,
                                    char_0x6F, char_0x66, char_0x20, char_0x5B,
                                    char_0x2F, char_0x3E, char_0x2C, char_0x20,
                                    char_0x3E, char_0x5D]
                                  (x : xs));
                     })
                else err_expecting
                       [char_0x6F, char_0x6E, char_0x65, char_0x20, char_0x6F,
                         char_0x66, char_0x20, char_0x5B, char_0x2F, char_0x3E,
                         char_0x2C, char_0x20, char_0x3E, char_0x5D]
                       (x : xs)));
oneof_closed_combined p q [] =
  err_expecting
    [char_0x6F, char_0x6E, char_0x65, char_0x20, char_0x6F, char_0x66,
      char_0x20, char_0x5B, char_0x2F, char_0x3E, char_0x2C, char_0x20,
      char_0x3E, char_0x5D]
    [];

exactly_close :: [Char] -> Sum [Char] ([Char], [Char]);
exactly_close (c : cs) =
  (if integer_of_char c == (62 :: Integer) then Inr ([char_0x3E], trim cs)
    else err_expecting [char_0x22, char_0x3E, char_0x22] (c : cs));
exactly_close [] = err_expecting [char_0x22, char_0x3E, char_0x22] [];

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

exactly_end :: [Char] -> Sum [Char] ([Char], [Char]);
exactly_end (c : d : cs) =
  (if integer_of_char c == (60 :: Integer) &&
        integer_of_char d == (47 :: Integer)
    then Inr ([char_0x3C, char_0x2F], trim cs)
    else err_expecting [char_0x22, char_0x3C, char_0x2F, char_0x22]
           (c : d : cs));
exactly_end [c] =
  err_expecting [char_0x22, char_0x3C, char_0x2F, char_0x22] [c];
exactly_end [] = err_expecting [char_0x22, char_0x3C, char_0x2F, char_0x22] [];

parse_text_main :: [Char] -> [Char] -> ([Char], [Char]);
parse_text_main (c : cs) res =
  (if integer_of_char c == (60 :: Integer) then (c : cs, reverse (trim res))
    else parse_text_main cs (c : res));
parse_text_main [] res = ([], reverse (trim res));

parse_text_impl :: forall a. [Char] -> Sum a (Maybe [Char], [Char]);
parse_text_impl cs =
  (case parse_text_main (trim cs) [] of {
    (rem, txt) ->
      (if null txt then Inr (Nothing, rem) else Inr (Just txt, rem));
  });

parse_text :: [Char] -> Sum [Char] (Maybe [Char], [Char]);
parse_text cs = parse_text_impl cs;

parse_nodes :: [Char] -> Sum [Char] ([Xml], [Char]);
parse_nodes (c : cs) =
  (if integer_of_char c == (60 :: Integer)
    then (if (case cs of {
               [] -> False;
               d : _ -> equal_char d char_0x2F;
             })
           then returna [] (c : cs)
           else binda parse_name
                  (\ n ->
                    binda parse_attributes
                      (\ atts ->
                        oneof_closed_combined
                          (binda parse_nodes
                            (\ csa -> returna (XML n atts [] : csa)))
                          (binda parse_nodes
                            (\ csa ->
                              binda exactly_end
                                (\ _ ->
                                  binda (exactly n)
                                    (\ _ ->
                                      binda exactly_close
(\ _ -> binda parse_nodes (\ ns -> returna (XML n atts csa : ns)))))))))
                  (trim cs))
    else binda parse_text
           (\ t -> binda parse_nodes (\ ns -> returna (XML_text (the t) : ns)))
           (c : cs));
parse_nodes [] = returna [] [];

parse_node :: [Char] -> Sum [Char] (Xml, [Char]);
parse_node =
  binda (exactly [char_0x3C])
    (\ _ ->
      binda parse_name
        (\ n ->
          binda parse_attributes
            (\ atts ->
              binda oneof_closed
                (\ e ->
                  (if e == [char_0x2F, char_0x3E] then returna (XML n atts [])
                    else binda parse_nodes
                           (\ cs ->
                             binda (exactly [char_0x3C, char_0x2F])
                               (\ _ ->
                                 binda (exactly n)
                                   (\ _ ->
                                     binda (exactly [char_0x3E])
                                       (\ _ -> returna (XML n atts cs))))))))));

parse_doc :: [Char] -> Sum [Char] (Xmldoc, [Char]);
parse_doc =
  binda (update_tokens remove_comments)
    (\ _ ->
      binda parse_header
        (\ h ->
          binda parse_node
            (\ xml -> binda eoi (\ _ -> returna (XMLDOC h xml)))));

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

modulo_integer :: Integer -> Integer -> Integer;
modulo_integer k l = snd (divmod_integer k l);

char_of_integer :: Integer -> Char;
char_of_integer k =
  Chr (if (0 :: Integer) <= k && k < (256 :: Integer) then k
        else modulo_integer k (256 :: Integer));

explode :: String -> [Char];
explode s =
  map char_of_integer
    (map (let ord k | (k < 128) = Prelude.toInteger k in ord . (Prelude.fromEnum :: Prelude.Char -> Prelude.Int))
      s);

xml :: String -> [([Char], [Char])] -> [Xml] -> Xml;
xml x = XML (explode x);

dps :: Xml -> [Xml];
dps (XML dPs uu [XML rules uv p]) = p;

char_0x0A :: Char;
char_0x0A = Chr (10 :: Integer);

shows_attr :: ([Char], [Char]) -> [Char] -> [Char];
shows_attr av =
  shows_prec_list zero_nat (fst av) .
    shows_string ([char_0x3D, char_0x22] ++ snd av ++ [char_0x22]);

shows_attrs :: [([Char], [Char])] -> [Char] -> [Char];
shows_attrs asa = foldr (\ a -> shows_string [char_0x20] . shows_attr a) asa;

replicate :: forall a. Nat -> a -> [a];
replicate n x =
  (if equal_nat n zero_nat then [] else x : replicate (minus_nat n one_nat) x);

shows_XML_indent :: [Char] -> Nat -> Xml -> [Char] -> [Char];
shows_XML_indent ind i (XML n a c) =
  shows_string [char_0x0A] .
    shows_string ind .
      shows_string [char_0x3C] .
        shows_prec_list zero_nat n .
          shows_attrs a .
            (if null c then shows_string [char_0x2F, char_0x3E]
              else shows_string [char_0x3E] .
                     foldr (shows_XML_indent (replicate i char_0x20 ++ ind) i)
                       c .
                       shows_string [char_0x0A] .
                         shows_string ind .
                           shows_string [char_0x3C, char_0x2F] .
                             shows_prec_list zero_nat n .
                               shows_string [char_0x3E]);
shows_XML_indent ind i (XML_text t) = shows_string t;

implode :: [Char] -> String;
implode cs =
  map (let chr k | (0 <= k && k < 128) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger)
    (map integer_of_char cs);

trs :: Xml -> [Xml];
trs (XML trs uu [XML rules uv r]) = r;
trs (XML v va []) =
  (error :: forall a. String -> (() -> a) -> a)
    ("trs structure fail: " ++
      implode (shows_XML_indent [] one_nat (XML v va []) []))
    (\ _ -> []);
trs (XML v va (XML_text ve : vd)) =
  (error :: forall a. String -> (() -> a) -> a)
    ("trs structure fail: " ++
      implode (shows_XML_indent [] one_nat (XML v va (XML_text ve : vd)) []))
    (\ _ -> []);
trs (XML v va (vc : ve : vf)) =
  (error :: forall a. String -> (() -> a) -> a)
    ("trs structure fail: " ++
      implode (shows_XML_indent [] one_nat (XML v va (vc : ve : vf)) []))
    (\ _ -> []);
trs (XML_text v) =
  (error :: forall a. String -> (() -> a) -> a)
    ("trs structure fail: " ++
      implode (shows_XML_indent [] one_nat (XML_text v) []))
    (\ _ -> []);

trs2a :: [Xml] -> Xml -> [Xml];
trs2a r s = let {
              sa = trs s;
              sS = set sa;
            } in filter (\ rule -> not (member rule sS)) r ++ sa;

trs2 :: Xml -> Xml -> [Xml];
trs2 r s = trs2a (trs r) s;

doc_of_string :: [Char] -> Sum [Char] Xmldoc;
doc_of_string s = bind (parse_doc s) (\ (doc, _) -> Inr doc);

xml_dps :: [Xml] -> Xml;
xml_dps p = xml "dps" [] [xml "rules" [] p];

xml_err :: [Char] -> String -> Xml;
xml_err s1 s2 =
  (error :: forall a. String -> (() -> a) -> a)
    ((("error at " ++ implode s1) ++ ": ") ++ s2)
    (\ _ -> XML_text [char_0x65, char_0x72, char_0x72, char_0x6F, char_0x72]);

xml_trs :: [Xml] -> Xml;
xml_trs p = xml "trs" [] [xml "rules" [] p];

comInput :: Xml -> [Xml];
comInput (XML trsIn uu [uv, r, s]) = trs2 r s;

sCrProof :: String;
sCrProof = "crProof";

sDpProof :: String;
sDpProof = "dpProof";

trsInput :: Xml -> [Xml];
trsInput (XML trsIn uu xs) =
  let {
    y = last xs;
  } in (if implode (tag y) == "relativeRules" then trs2 (hd xs) y
         else trs (hd xs));

sComProof :: String;
sComProof = "comProof";

modulo_nat :: Nat -> Nat -> Nat;
modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

string_of_digit :: Nat -> [Char];
string_of_digit n =
  (if equal_nat n zero_nat then [char_0x30]
    else (if equal_nat n one_nat then [char_0x31]
           else (if equal_nat n (nat_of_integer (2 :: Integer)) then [char_0x32]
                  else (if equal_nat n (nat_of_integer (3 :: Integer))
                         then [char_0x33]
                         else (if equal_nat n (nat_of_integer (4 :: Integer))
                                then [char_0x34]
                                else (if equal_nat n
   (nat_of_integer (5 :: Integer))
                                       then [char_0x35]
                                       else (if equal_nat n
          (nat_of_integer (6 :: Integer))
      then [char_0x36]
      else (if equal_nat n (nat_of_integer (7 :: Integer)) then [char_0x37]
             else (if equal_nat n (nat_of_integer (8 :: Integer))
                    then [char_0x38] else [char_0x39])))))))));

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

showsp_nat :: Nat -> Nat -> [Char] -> [Char];
showsp_nat p n =
  (if less_nat n (nat_of_integer (10 :: Integer))
    then shows_string (string_of_digit n)
    else showsp_nat p (divide_nat n (nat_of_integer (10 :: Integer))) .
           shows_string
             (string_of_digit (modulo_nat n (nat_of_integer (10 :: Integer)))));

shows_prec_nat :: Nat -> Nat -> [Char] -> [Char];
shows_prec_nat = showsp_nat;

signature :: Set Xml -> [Xml] -> [Xml];
signature s (XML tag asa xs : ys) =
  (if implode tag == "funapp"
    then (case xs of {
           f : xsa ->
             let {
               rest = xsa ++ ys;
             } in (if member f s then signature s rest
                    else xml "symbol" []
                           [f, xml "arity" []
                                 [XML_text
                                    (shows_prec_nat zero_nat (size_list xsa)
                                      [])]] :
                           signature (inserta f s) rest);
         })
    else signature s (xs ++ ys));
signature s (XML_text v : ys) = signature s ys;
signature s [] = [];

union_trs :: Xml -> Xml -> Xml;
union_trs (XML trs uu [XML rules uv r1]) (XML uw ux [XML uy uz r2]) =
  XML trs [] [XML rules [] (r1 ++ r2)];

remain_dps :: [Xml] -> Xml -> [Xml];
remain_dps c (XML dPs uu [XML rules uv pdel]) =
  let {
    del = set pdel;
  } in filter (\ r -> not (member r del)) c;

remain_trs :: [Xml] -> Xml -> [Xml];
remain_trs c (XML trs uu [XML rules uv del]) =
  let {
    dela = set del;
  } in filter (\ r -> not (member r dela)) c;

remove_arg :: Xml -> Xml;
remove_arg (XML_text s) = XML_text s;
remove_arg (XML tag asa xs) =
  let {
    xsa = map remove_arg xs;
  } in (if tag == [char_0x61, char_0x72, char_0x67] then hd xsa
         else XML tag asa xsa);

deleted_dps :: [Xml] -> Xml -> Xml;
deleted_dps c (XML dPs uu [XML rules uv p]) =
  XML dPs [] [XML rules [] (let {
                              remain = set p;
                            } in filter (\ r -> not (member r remain)) c)];

deleted_trs :: [Xml] -> Xml -> Xml;
deleted_trs c (XML trs uu [XML rules uv r]) =
  XML trs [] [XML rules [] (let {
                              remain = set r;
                            } in filter (\ ra -> not (member ra remain)) c)];

reltrsInput :: Xml -> ([Xml], [Xml]);
reltrsInput (XML trsIn uu xs) =
  let {
    y = last xs;
  } in (if implode (tag y) == "relativeRules" then (trs (hd xs), trs y)
         else (trs (hd xs), []));

replace_dps :: forall a. (Eq a) => [a] -> a -> [a] -> [a];
replace_dps xs x ys = let {
                        xsa = filter (\ y -> not (y == x)) xs;
                      } in xsa ++ filter (\ y -> not (membera xsa y)) ys;

sCrDisproof :: String;
sCrDisproof = "crDisproof";

deleted_trs2 :: [Xml] -> Xml -> Xml -> Xml;
deleted_trs2 c (XML trsa uu [XML rulesa uv ra]) (XML trs uw [XML rules ux r]) =
  XML trsa [] [XML rulesa [] (let {
                                remain = set (ra ++ r);
                              } in filter (\ rb -> not (member rb remain)) c)];

rule_indices_main ::
  Nat ->
    (Nat, ([([Char], Xml)], (Mapping Xml [Char], Mapping [Char] Xml))) ->
      Xml ->
        (Xml, (Nat, ([([Char], Xml)],
                      (Mapping Xml [Char], Mapping [Char] Xml))));
rule_indices_main i info (XML_text s) = (XML_text s, info);
rule_indices_main i info (XML tag atts xs) =
  (if implode tag == "rule" && equal_nat i zero_nat
    then let {
           x = XML tag atts xs;
         } in (case info of {
                (next, (list, (m, ma))) ->
                  (case lookupa m x of {
                    Nothing ->
                      let {
                        s = shows_prec_nat zero_nat next [];
                      } in (xml "ruleIndex" [] [XML_text s],
                             (suc next,
                               ((s, x) : list, (update x s m, update s x ma))));
                    Just idx ->
                      (xml "ruleIndex" []
                         [XML_text (shows_prec_list zero_nat idx [])],
                        info);
                  });
              })
    else let {
           j = (if membera
                     ["probs", "ctrsInput", "infeasibilityInput",
                       "conditionalRewriteStep", "inlineConditions",
                       "infeasibleRules", "unfeasibilityProof",
                       "rightInlineConditions", "leftInlineConditions",
                       "inlinedRules", "ifritRules"]
                     (implode tag)
                 then nat_of_integer (2 :: Integer) else minus_nat i one_nat);
         } in (case rule_indices_main_list j info xs of {
                (xsa, a) -> (XML tag atts xsa, a);
              }));

rule_indices_main_list ::
  Nat ->
    (Nat, ([([Char], Xml)], (Mapping Xml [Char], Mapping [Char] Xml))) ->
      [Xml] ->
        ([Xml],
          (Nat, ([([Char], Xml)], (Mapping Xml [Char], Mapping [Char] Xml))));
rule_indices_main_list i info [] = ([], info);
rule_indices_main_list i info (x : xs) =
  (case rule_indices_main i info x of {
    (xa, infoa) -> (case rule_indices_main_list i infoa xs of {
                     (xsa, a) -> (xa : xsa, a);
                   });
  });

rule_indices :: Xml -> (Xml, (Xml, Mapping [Char] Xml));
rule_indices x =
  (case rule_indices_main zero_nat (one_nat, ([], (emptya, emptya))) x of {
    (xa, (_, (table, (_, m)))) ->
      let {
        tab = xml "ruleTable" []
                (map (\ (i, r) ->
                       xml "indexToRule" [] [xml "index" [] [XML_text i], r])
                  (reverse table));
      } in (xa, (tab, m));
  });

sComDisproof :: String;
sComDisproof = "comDisproof";

term_indices_main ::
  (Nat, ([([Char], Xml)], Mapping [Xml] [Char])) ->
    Xml -> (Xml, (Nat, ([([Char], Xml)], Mapping [Xml] [Char])));
term_indices_main info (XML_text s) = (XML_text s, info);
term_indices_main info (XML tag atts xs) =
  (case term_indices_main_list info xs of {
    (xsa, infoa) ->
      let {
        x = XML tag atts xsa;
      } in (if implode tag == "funapp"
             then (case infoa of {
                    (next, (list, m)) ->
                      (case lookupa m xsa of {
                        Nothing ->
                          let {
                            s = shows_prec_nat zero_nat next [];
                          } in (xml "termIndex" [] [XML_text s],
                                 (suc next, ((s, x) : list, update xsa s m)));
                        Just idx ->
                          (xml "termIndex" []
                             [XML_text (shows_prec_list zero_nat idx [])],
                            info);
                      });
                  })
             else (x, infoa));
  });

term_indices_main_list ::
  (Nat, ([([Char], Xml)], Mapping [Xml] [Char])) ->
    [Xml] -> ([Xml], (Nat, ([([Char], Xml)], Mapping [Xml] [Char])));
term_indices_main_list info [] = ([], info);
term_indices_main_list info (x : xs) =
  (case term_indices_main info x of {
    (xa, infoa) -> (case term_indices_main_list infoa xs of {
                     (xsa, a) -> (xa : xsa, a);
                   });
  });

term_indices :: Xml -> (Xml, Xml);
term_indices x =
  (case term_indices_main (one_nat, ([], emptya)) x of {
    (xa, (_, (table, _))) ->
      let {
        a = xml "termIndexTable" []
              (map (\ (i, r) ->
                     xml "indexToTerm" [] [xml "index" [] [XML_text i], r])
                (reverse table));
      } in (xa, a);
  });

sRelativeNonterminationProof :: String;
sRelativeNonterminationProof = "relativeNonterminationProof";

sRelativeTerminationProof :: String;
sRelativeTerminationProof = "relativeTerminationProof";

sTrsNonterminationProof :: String;
sTrsNonterminationProof = "trsNonterminationProof";

sDpNonterminationProof :: String;
sDpNonterminationProof = "dpNonterminationProof";

flip_deleted_dps_nt :: [Xml] -> [Xml] -> Xml -> Xml;
flip_deleted_dps_nt p r (XML dpprf uu children) =
  (if implode dpprf == sDpNonterminationProof
    then (case children of {
           [XML taga _ xs] ->
             XML dpprf []
               [(if membera ["loop", "nonLoop"] (implode taga)
                  then XML taga [] xs
                  else (if implode taga == "dpRuleRemoval"
                         then (case xs of {
                                x1 : xs1 ->
                                  (case (if implode (tag x1) == "dps"
  then (x1, xs1) else (xml_dps p, x1 : xs1))
                                    of {
                                    (pa, x2 : xs2) ->
                                      (case
(if implode (tag x2) == "trs" then (x2, xs2) else (xml_trs r, x2 : xs2)) of {
(ra, [prf]) ->
  XML taga []
    [deleted_dps p pa, deleted_trs r ra,
      flip_deleted_dps_nt (dps pa) (trs ra) prf];
                                      });
                                  });
                              })
                         else (if membera
                                    ["innermostLhssRemovalProc",
                                      "innermostLhssIncreaseProc",
                                      "switchFullStrategyProc"]
                                    (implode taga)
                                then (case xs of {
                                       [x1, prf] ->
 XML taga [] [x1, flip_deleted_dps_nt p r prf];
                                     })
                                else (if implode taga == "narrowingProc"
                                       then (case xs of {
      [rule, x1, pa, prf] ->
        XML taga []
          [rule, x1, pa,
            flip_deleted_dps_nt (replace_dps p rule (dps pa)) r prf];
    })
                                       else (if implode taga ==
          "instantiationProc"
      then (case xs of {
             [pa, prf] -> XML taga [] [pa, flip_deleted_dps_nt (dps pa) r prf];
           })
      else (if implode taga == "rewritingProc"
             then (case xs of {
                    [rule, x1, rulea, x2, prf] ->
                      XML taga []
                        [rule, x1, rulea, x2,
                          flip_deleted_dps_nt (replace_dps p rule [rulea]) r
                            prf];
                  })
             else xml_err taga "flip_dps_nt unknown tag"))))))];
         })
    else xml_err dpprf " is not dpNonterminationProof");
flip_deleted_dps_nt p r (XML_text uv) =
  xml_err [char_0x74, char_0x65, char_0x78, char_0x74] "flip_dps_nt: hit text";

flip_deleted_trs_nt :: [Xml] -> Xml -> Xml;
flip_deleted_trs_nt r (XML trsprf uu children) =
  (if implode trsprf == sTrsNonterminationProof
    then (case children of {
           [XML tag _ xs] ->
             XML trsprf []
               [(if membera
                      ["rightGroundNontermination", "variableConditionViolated",
                        "loop", "nonLoop", "nonterminatingSRS",
                        "notWNTreeAutomaton"]
                      (implode tag)
                  then XML tag [] xs
                  else (if implode tag == "ruleRemoval"
                         then (case xs of {
                                [ra, prf] ->
                                  XML tag []
                                    [deleted_trs r ra,
                                      flip_deleted_trs_nt (trs ra) prf];
                              })
                         else (if membera
                                    ["innermostLhssIncrease",
                                      "switchFullStrategy"]
                                    (implode tag)
                                then (case xs of {
                                       [x1, prf] ->
 XML tag [] [x1, flip_deleted_trs_nt r prf];
                                     })
                                else (if implode tag == "constantToUnary"
                                       then (case xs of {
      [x1, x2, ra, prf] ->
        XML tag [] [x1, x2, ra, flip_deleted_trs_nt (trs ra) prf];
    })
                                       else (if implode tag == "stringReversal"
      then (case xs of {
             [ra, prf] -> XML tag [] [ra, flip_deleted_trs_nt (trs ra) prf];
           })
      else (if implode tag == "dpTrans"
             then (case xs of {
                    [p, x1, prf] ->
                      XML tag [] [p, x1, flip_deleted_dps_nt (dps p) r prf];
                  })
             else (if implode tag == "uncurry"
                    then (case xs of {
                           [x1, ra, prf] ->
                             XML tag []
                               [x1, ra, flip_deleted_trs_nt (trs ra) prf];
                         })
                    else xml_err tag "flip_dps_nt unknown tag")))))))];
         })
    else xml_err trsprf " is not trsNonterminationProof");
flip_deleted_trs_nt r (XML_text uv) =
  xml_err [char_0x74, char_0x65, char_0x78, char_0x74] "flip_trs_nt: hit text";

flip_deleted_reltrs_nt :: [Xml] -> [Xml] -> Xml -> Xml;
flip_deleted_reltrs_nt r s (XML trsprf uu children) =
  (if implode trsprf == sRelativeNonterminationProof
    then (case children of {
           [XML tag _ xs] ->
             XML trsprf []
               [(if membera ["variableConditionViolated", "loop"] (implode tag)
                  then XML tag [] xs
                  else (if implode tag == "ruleRemoval"
                         then (case xs of {
                                [ra, sa, prf] ->
                                  XML tag []
                                    [deleted_trs r ra, deleted_trs s sa,
                                      flip_deleted_reltrs_nt (trs ra) (trs sa)
prf];
                              })
                         else (if implode tag == "stringReversal"
                                then (case xs of {
                                       [ra, sa, prf] ->
 XML tag [] [ra, sa, flip_deleted_reltrs_nt (trs ra) (trs sa) prf];
                                     })
                                else (if implode tag == "trsNonterminationProof"
                                       then flip_deleted_trs_nt r (hd children)
                                       else xml_err tag
      "flip_dps_nt unknown tag"))))];
         })
    else xml_err trsprf " is not relativeNonterminationProof");
flip_deleted_reltrs_nt r s (XML_text uv) =
  xml_err [char_0x74, char_0x65, char_0x78, char_0x74]
    "flip_reltrs_nt: hit text";

sTrsTerminationProof :: String;
sTrsTerminationProof = "trsTerminationProof";

sQuasiReductiveProof :: String;
sQuasiReductiveProof = "quasiReductiveProof";

sEquationalDisproof :: String;
sEquationalDisproof = "equationalDisproof";

sConditionalCrProof :: String;
sConditionalCrProof = "conditionalCrProof";

sCompletionProof :: String;
sCompletionProof = "completionProof";

isEqualityRule :: Mapping [Char] Xml -> Xml -> Bool;
isEqualityRule ruleMap (XML uu uv [XML_text ind]) =
  (case lookupa ruleMap ind of {
    Just (XML _ _ [l, r]) -> equal_xml l r;
  });

flip_deleted_trs :: Mapping [Char] Xml -> [Xml] -> Xml -> Xml;
flip_deleted_trs ruleMap r (XML trsprf uw children) =
  (if membera [sTrsTerminationProof, sRelativeTerminationProof] (implode trsprf)
    then (case children of {
           [XML tag _ xs] ->
             XML trsprf []
               [(if membera ["rIsEmpty", "rightGroundTermination", "bounds"]
                      (implode tag)
                  then XML tag [] xs
                  else (if implode tag == "ruleRemoval"
                         then (case xs of {
                                [x1, ra, prf] ->
                                  XML tag []
                                    [x1, deleted_trs r ra,
                                      flip_deleted_trs ruleMap (trs ra) prf];
                                [x1, ra, prf, prfa] ->
                                  XML tag []
                                    [x1, deleted_trs2 r ra prf,
                                      flip_deleted_trs ruleMap (trs2 ra prf)
prfa];
                              })
                         else (if implode tag == "dpTrans"
                                then (case xs of {
                                       [p, x1, prf] ->
 XML tag [] [p, x1, flip_deleted_dps ruleMap (dps p) r prf];
                                     })
                                else (if implode tag == "semlab"
                                       then (case xs of {
      [x1, ra, s] -> XML tag [] [x1, ra, flip_deleted_trs ruleMap (trs ra) s];
      [x1, ra, s, prf] ->
        XML tag []
          [x1, union_trs ra s, flip_deleted_trs ruleMap (trs2 ra s) prf];
    })
                                       else (if implode tag == "split"
      then (case xs of {
             [ra, prf, prfa] ->
               XML tag []
                 [ra, flip_deleted_trs ruleMap r prf,
                   flip_deleted_trs ruleMap (remain_trs r ra) prfa];
           })
      else (if implode tag == "uncurry"
             then (case xs of {
                    [x1, ra, s] ->
                      XML tag [] [x1, ra, flip_deleted_trs ruleMap (trs ra) s];
                    [x1, ra, s, prf] ->
                      XML tag []
                        [x1, union_trs ra s,
                          flip_deleted_trs ruleMap (trs2 ra s) prf];
                  })
             else (if implode tag == "stringReversal"
                    then (case xs of {
                           [ra, s] ->
                             XML tag []
                               [ra, flip_deleted_trs ruleMap (trs ra) s];
                           [ra, s, prf] ->
                             XML tag []
                               [union_trs ra s,
                                 flip_deleted_trs ruleMap (trs2 ra s) prf];
                         })
                    else (if implode tag == "removeNonApplicableRules"
                           then (case xs of {
                                  [ra, prf] ->
                                    XML tag []
                                      [ra,
flip_deleted_trs ruleMap (remain_trs r ra) prf];
                                })
                           else (if implode tag == "flatContextClosure"
                                  then (case xs of {
 [x1, ra, s] -> XML tag [] [x1, ra, flip_deleted_trs ruleMap (trs ra) s];
 [x1, ra, s, prf] ->
   XML tag [] [x1, union_trs ra s, flip_deleted_trs ruleMap (trs2 ra s) prf];
                                       })
                                  else (if implode tag == "constantToUnary"
 then (case xs of {
        [x1, x2, ra, s] ->
          XML tag [] [x1, x2, ra, flip_deleted_trs ruleMap (trs ra) s];
        [x1, x2, ra, s, prf] ->
          XML tag []
            [x1, x2, union_trs ra s, flip_deleted_trs ruleMap (trs2 ra s) prf];
      })
 else (if implode tag == "equalityRemoval"
        then (case xs of {
               [prf] ->
                 XML tag []
                   [flip_deleted_trs ruleMap
                      (filter (\ rule -> not (isEqualityRule ruleMap rule)) r)
                      prf];
             })
        else (if implode tag == "switchInnermost"
               then (case xs of {
                      [x1, prf] ->
                        XML tag [] [x1, flip_deleted_trs ruleMap r prf];
                    })
               else (if implode tag == "sIsEmpty"
                      then (case xs of {
                             [prf] ->
                               XML tag [] [flip_deleted_trs ruleMap r prf];
                           })
                      else xml_err tag
                             "flip_trs unknown or unsupported tag")))))))))))))];
         })
    else xml_err trsprf " is not trs or relative termination proof");
flip_deleted_trs ruleMap r (XML_text ux) =
  xml_err [char_0x74, char_0x65, char_0x78, char_0x74] "flip_trs: hit text";

flip_deleted_dps :: Mapping [Char] Xml -> [Xml] -> [Xml] -> Xml -> Xml;
flip_deleted_dps ruleMap p r (XML dpprf uu childrena) =
  (if implode dpprf == sDpProof
    then (case childrena of {
           [XML taga _ xs] ->
             XML dpprf []
               [(if membera ["pIsEmpty", "sizeChangeProc"] (implode taga)
                  then XML taga [] xs
                  else (if implode taga == "depGraphProc"
                         then XML taga []
                                (map (\ (XML c _ tuple) ->
                                       (case reverse tuple of {
 l : ls ->
   XML c []
     (reverse
       ((if implode (tag l) == sDpProof
          then flip_deleted_dps ruleMap (dps (hd tuple)) r l else l) :
         ls));
                                       }))
                                  xs)
                         else (if implode taga == "monoRedPairProc"
                                then (case xs of {
                                       [x1, pa, ra, prf] ->
 XML taga []
   [x1, deleted_dps p pa, deleted_trs r ra,
     flip_deleted_dps ruleMap (dps pa) (trs ra) prf];
                                     })
                                else (if implode taga == "monoRedPairUrProc"
                                       then (case xs of {
      [x1, pa, ra, ur, prf] ->
        XML taga []
          [x1, deleted_dps p pa, deleted_trs (trs ur) ra, ur,
            flip_deleted_dps ruleMap (dps pa) (trs ra) prf];
    })
                                       else (if membera
          ["redPairProc", "redPairUrProc"] (implode taga)
      then (case xs of {
             [x1, pa, prf] ->
               XML taga []
                 [x1, deleted_dps p pa,
                   flip_deleted_dps ruleMap (dps pa) r prf];
             [x1, pa, prf, prfa] ->
               XML taga []
                 [x1, deleted_dps p pa, prf,
                   flip_deleted_dps ruleMap (dps pa) r prfa];
           })
      else (if implode taga == "subtermProc"
             then (case reverse xs of {
                    prf : pa : ys ->
                      (if implode (tag (hd xs)) == "argumentFilter"
                        then XML taga []
                               (reverse
                                 (flip_deleted_dps ruleMap (dps pa) r prf :
                                   deleted_dps p pa : ys))
                        else XML taga []
                               (reverse
                                 (flip_deleted_dps ruleMap (remain_dps p pa) r
                                    prf :
                                   pa : ys)));
                  })
             else (if implode taga == "innermostMonoRedPairProc"
                    then (case xs of {
                           [x1, XML _ _ [pa, ra], prf] ->
                             XML taga []
                               [x1, pa, ra,
                                 flip_deleted_dps ruleMap (remain_dps p pa)
                                   (remain_trs r ra) prf];
                         })
                    else (if membera ["flatContextClosureProc", "uncurryProc"]
                               (implode taga)
                           then (case xs of {
                                  [x1, x2, pa, ra] ->
                                    XML taga []
                                      [x1, x2, pa,
flip_deleted_dps ruleMap (dps x2) (trs pa) ra];
                                  [x1, x2, pa, ra, prf] ->
                                    XML taga []
                                      [x1, x2, pa, ra,
flip_deleted_dps ruleMap (dps pa) (trs ra) prf];
                                })
                           else (if membera ["semlabProc", "argumentFilterProc"]
                                      (implode taga)
                                  then (case xs of {
 [x1, pa, ra, x2] ->
   XML taga [] [x1, pa, ra, flip_deleted_dps ruleMap (dps pa) (trs ra) x2];
 [x1, pa, ra, x2, prf] ->
   XML taga [] [x1, pa, ra, x2, flip_deleted_dps ruleMap (dps pa) (trs ra) prf];
                                       })
                                  else (if implode taga == "generalRedPairProc"
 then (case xs of {
        [x1, pa, pb, x2, prf] ->
          XML taga []
            [x1, pa, pb, x2,
              flip_deleted_dps ruleMap
                (let {
                   del1 = set (dps pa);
                   del2 = set (dps pb);
                 } in filter (\ ra -> not (member ra del1 && member ra del2)) p)
                r prf];
        [x1, pa, pb, x2, prf, prfa] ->
          XML taga []
            [x1, pa, pb, x2, flip_deleted_dps ruleMap (remain_dps p pa) r prf,
              flip_deleted_dps ruleMap (remain_dps p pb) r prfa];
      })
 else (if implode taga == "splitProc"
        then (case xs of {
               [pa, ra, prf, prfa] ->
                 XML taga []
                   [pa, ra, flip_deleted_dps ruleMap p r prf,
                     flip_deleted_dps ruleMap (remain_dps p pa)
                       (remain_trs r ra) prfa];
             })
        else (if implode taga == "narrowingProc"
               then (case xs of {
                      [rule, x1, pa, prf] ->
                        XML taga []
                          [rule, x1, pa,
                            flip_deleted_dps ruleMap
                              (replace_dps p rule (dps pa)) r prf];
                    })
               else (if membera
                          ["instantiationProc", "forwardInstantiationProc"]
                          (implode taga)
                      then (case xs of {
                             [rule, pa, prf] ->
                               XML taga []
                                 [rule, pa,
                                   flip_deleted_dps ruleMap
                                     (replace_dps p rule (dps pa)) r prf];
                             [rule, pa, prf, prfa] ->
                               XML taga []
                                 [rule, pa, prf,
                                   flip_deleted_dps ruleMap
                                     (replace_dps p rule (dps pa)) r prfa];
                           })
                      else (if implode taga == "complexConstantRemovalProc"
                             then (case xs of {
                                    [x1, rm, prf] ->
                                      XML taga []
[x1, rm,
  flip_deleted_dps ruleMap (map (\ (XML _ _ [_, ra]) -> ra) (children rm)) r
    prf];
                                  })
                             else (if implode taga == "rewritingProc"
                                    then (case xs of {
   [rule, x1, rulea, x2, prf] ->
     XML taga []
       [rule, x1, rulea, x2,
         flip_deleted_dps ruleMap (replace_dps p rule [rulea]) r prf];
 })
                                    else (if membera
       ["usableRulesProc", "innermostLhssRemovalProc", "switchInnermostProc"]
       (implode taga)
   then (case xs of {
          [x1, prf] -> XML taga [] [x1, flip_deleted_dps ruleMap p r prf];
        })
   else (if implode taga == "switchToTRS"
          then (case xs of {
                 [prf] -> XML taga [] [flip_deleted_trs ruleMap (p ++ r) prf];
               })
          else xml_err taga "flip_dps unknown tag")))))))))))))))))];
         })
    else xml_err dpprf " is not dpProof");
flip_deleted_dps ruleMap p r (XML_text uv) =
  xml_err [char_0x74, char_0x65, char_0x78, char_0x74] "flip_dps: hit text";

flip_deleted_compl :: Mapping [Char] Xml -> [Xml] -> Xml -> Xml;
flip_deleted_compl ruleMap r (XML cprf uu children) =
  (if implode cprf == sCompletionProof
    then (case children of {
           [x1, prf, x2] ->
             XML cprf [] [x1, flip_deleted_trs ruleMap r prf, x2];
         })
    else xml_err cprf " is not completion proof");
flip_deleted_compl ruleMap r (XML_text uv) =
  xml_err [char_0x74, char_0x65, char_0x78, char_0x74]
    "flip_completion: hit text";

flip_deleted_cond :: Mapping [Char] Xml -> Xml -> Xml;
flip_deleted_cond ruleMap (XML cprf uu childrena) =
  (if implode cprf == sQuasiReductiveProof
    then (case childrena of {
           [XML unrav _ [info, prf]] ->
             XML cprf []
               [XML unrav []
                  [info,
                    flip_deleted_trs ruleMap
                      (concatMap (\ (XML _ _ (_ : rs)) -> rs) (children info))
                      prf]];
         })
    else xml_err cprf " in not conditional termination proof");

sEquationalProof :: String;
sEquationalProof = "equationalProof";

flip_deleted_cr :: Mapping [Char] Xml -> [Xml] -> Xml -> Xml;
flip_deleted_cr ruleMap r (XML trsprf uu children) =
  (if membera [sCrProof, sCrDisproof, sComProof, sComDisproof] (implode trsprf)
    then (case children of {
           [XML taga _ xs] ->
             XML trsprf []
               [(if membera
                      ["orthogonal", "stronglyClosed", "pcpClosed",
                        "ruleLabeling", "developmentClosed",
                        "modularityDisjoint", "nonJoinableFork",
                        "pcpRuleLabeling", "parallelClosed"]
                      (implode taga)
                  then XML taga [] xs
                  else (if membera ["wcrAndSN", "nonWcrAndSN"] (implode taga)
                         then (case xs of {
                                [x1, prf] ->
                                  XML taga []
                                    [x1, flip_deleted_trs ruleMap r prf];
                              })
                         else (if implode taga == "compositionalPcpRuleLabeling"
                                then (case reverse xs of {
                                       prf : ra : r2 : ys ->
 XML taga []
   (reverse
     (flip_deleted_cr ruleMap
        (if implode (tag r2) == "trs" then trs2 ra r2 else trs ra) prf :
       ra : r2 : ys));
                                     })
                                else (if membera ["swapTRSs", "switchToCrProof"]
   (implode taga)
                                       then (case xs of {
      [prf] -> XML taga [] [flip_deleted_cr ruleMap r prf];
    })
                                       else (if implode taga ==
          "compositionalPcp"
      then (case xs of {
             [c, x1, prf] ->
               XML taga [] [c, x1, flip_deleted_cr ruleMap (trs c) prf];
           })
      else (if implode taga == "compositionalPcps"
             then (case xs of {
                    [c, p, x1, x2, prf, prfa] ->
                      XML taga []
                        [c, p, x1, x2, flip_deleted_trs ruleMap (trs2a r p) prf,
                          flip_deleted_cr ruleMap (trs c) prfa];
                    [c, p, x1, x2, prf, prfa, x4, prfaa, prf_a] ->
                      XML taga []
                        [c, p, x1, x2, prf, prfa, x4,
                          flip_deleted_trs ruleMap (trs2a r x1) prfaa,
                          flip_deleted_cr ruleMap (trs2 c p) prf_a];
                  })
             else (if implode taga == "criticalPairClosingSystem"
                    then (case xs of {
                           [ra, prf, x1] ->
                             XML taga []
                               [ra, flip_deleted_trs ruleMap (trs ra) prf, x1];
                         })
                    else (if implode taga == "decreasingDiagrams"
                           then (case xs of {
                                  [prf] -> XML taga [] [prf];
                                  [prf, x1] ->
                                    XML taga []
                                      [flip_deleted_trs ruleMap r prf, x1];
                                })
                           else (if implode taga == "redundantRules"
                                  then (case reverse xs of {
 prf : ys ->
   XML taga [] (reverse (flip_deleted_cr ruleMap (trs (hd xs)) prf : ys));
                                       })
                                  else (if implode taga ==
     "persistentDecomposition"
 then (case xs of {
        x1 : ys ->
          XML taga []
            (x1 : map (\ (XML com _ [ra, prf]) ->
                        XML com [] [ra, flip_deleted_cr ruleMap (trs ra) prf])
                    ys);
      })
 else xml_err taga "flip_cr unknown or unsupported tag"))))))))))];
         })
    else xml_err trsprf " is not cr or com proof");
flip_deleted_cr ruleMap r (XML_text uv) =
  xml_err [char_0x74, char_0x65, char_0x78, char_0x74] "flip_cr: hit text";

flip_deleted_ccr :: Mapping [Char] Xml -> Xml -> Xml;
flip_deleted_ccr ruleMap (XML trsprf uu childrena) =
  (if implode trsprf == sConditionalCrProof
    then (case childrena of {
           [XML tag _ xs] ->
             XML trsprf []
               [(if membera
                      ["almostOrthogonal",
                        "almostOrthogonalModuloInfeasibility"]
                      (implode tag)
                  then XML tag [] xs
                  else (if implode tag == "inlineConditions"
                         then (case xs of {
                                [x1, x2, prf] ->
                                  XML tag []
                                    [x1, x2, flip_deleted_ccr ruleMap prf];
                              })
                         else (if implode tag == "al94"
                                then (case xs of {
                                       prf : ys ->
 XML tag [] (flip_deleted_cond ruleMap prf : ys);
                                     })
                                else (if implode tag == "unconditional"
                                       then (case xs of {
      [prf] ->
        XML tag []
          [flip_deleted_cr ruleMap
             ((error :: forall a. String -> (() -> a) -> a)
               "trs below unconditional" (\ _ -> []))
             prf];
    })
                                       else (if implode tag == "unraveling"
      then (case xs of {
             [info, prf] ->
               XML tag []
                 [info,
                   flip_deleted_cr ruleMap
                     (concatMap (\ (XML _ _ (_ : rs)) -> rs) (children info))
                     prf];
           })
      else (if implode tag == "infeasibleRuleRemoval"
             then (case xs of {
                    [r, prf] -> XML tag [] [r, flip_deleted_ccr ruleMap prf];
                  })
             else xml_err tag "flip_cr unknown or unsupported tag"))))))];
         })
    else xml_err trsprf " is not conditional cr proof");
flip_deleted_ccr ruleMap (XML_text uv) =
  xml_err [char_0x74, char_0x65, char_0x78, char_0x74]
    "flip_conditional_cr: hit text";

flip_deleted_eq :: Mapping [Char] Xml -> Xml -> Xml;
flip_deleted_eq ruleMap (XML trsprf uu children) =
  (if membera [sEquationalProof, sEquationalDisproof] (implode trsprf)
    then (case children of {
           [XML tag _ xs] ->
             XML trsprf []
               [(if membera
                      ["equationalProofTree", "convertibleInstance",
                        "conversion", "subsumptionProof"]
                      (implode tag)
                  then XML tag [] xs
                  else (if implode tag == "completionAndNormalization"
                         then (case xs of {
                                [r, prf] ->
                                  XML tag []
                                    [r, flip_deleted_compl ruleMap (trs r) prf];
                              })
                         else xml_err tag
                                "flip_eq unknown or unsupported tag"))];
         })
    else xml_err trsprf " is not equational (dis) proof");
flip_deleted_eq ruleMap (XML_text uv) =
  xml_err [char_0x74, char_0x65, char_0x78, char_0x74]
    "flip_conditional_eq: hit text";

flip_deletion :: Mapping [Char] Xml -> Xml -> Xml;
flip_deletion ruleMap
  (XML cp asa [XML input uu [inp], vers, XML proof uv [prf], orig]) =
  XML cp asa
    [XML input [] [inp], vers,
      XML proof []
        [(if implode (tag prf) == sDpProof
           then (case inp of {
                  XML _ _ (r : p : _) ->
                    flip_deleted_dps ruleMap (dps p) (trs r) prf;
                })
           else (if membera [sTrsTerminationProof, sRelativeTerminationProof]
                      (implode (tag prf))
                  then flip_deleted_trs ruleMap (trsInput inp) prf
                  else (if membera [sCrProof, sCrDisproof] (implode (tag prf))
                         then flip_deleted_cr ruleMap (trsInput inp) prf
                         else (if membera [sComProof, sComDisproof]
                                    (implode (tag prf))
                                then flip_deleted_cr ruleMap (comInput inp) prf
                                else (if implode (tag prf) ==
   sQuasiReductiveProof
                                       then flip_deleted_cond ruleMap prf
                                       else (if implode (tag prf) ==
          sConditionalCrProof
      then flip_deleted_ccr ruleMap prf
      else (if implode (tag prf) == sCompletionProof
             then (case inp of {
                    XML _ _ [_, r] -> flip_deleted_compl ruleMap (trs r) prf;
                  })
             else (if membera [sEquationalProof, sEquationalDisproof]
                        (implode (tag prf))
                    then flip_deleted_eq ruleMap prf
                    else (if implode (tag prf) == sDpNonterminationProof
                           then (case inp of {
                                  XML _ _ (r : p : _) ->
                                    flip_deleted_dps_nt (dps p) (trs r) prf;
                                })
                           else (if implode (tag prf) == sTrsNonterminationProof
                                  then flip_deleted_trs_nt (trsInput inp) prf
                                  else (if implode (tag prf) ==
     sRelativeNonterminationProof
 then (case reltrsInput inp of {
        (r, s) -> flip_deleted_reltrs_nt r s prf;
      })
 else prf)))))))))))],
      orig];

bot_set :: forall a. (Linorder a) => Set a;
bot_set = Setm emptya;

xml_to_final_string :: Xml -> String;
xml_to_final_string x =
  implode
    (filter (\ y -> not (equal_char char_0x0A y))
      (shows_XML_indent [] zero_nat x []));

term_index_optional :: Bool -> Xml -> (Xml, [Xml]);
term_index_optional use x =
  (if use then (case term_indices x of {
                 (xa, tiTable) -> (xa, [tiTable]);
               })
    else (x, []));

signature_optional :: Xml -> [Xml];
signature_optional x =
  (case x of {
    XML cp _ [] ->
      (error :: forall a. String -> (() -> a) -> a) ("sigopt: " ++ implode cp)
        (\ _ -> []);
    XML cp _ (XML _ _ [] : _) ->
      (error :: forall a. String -> (() -> a) -> a) ("sigopt: " ++ implode cp)
        (\ _ -> []);
    XML _ _ (XML _ _ [inp] : _) ->
      (if implode (tag inp) == "trsInput"
        then let {
               rls = trsInput inp;
             } in [xml "signature" [] (signature bot_set rls)]
        else []);
    XML cp _ (XML _ _ (_ : _ : _) : _) ->
      (error :: forall a. String -> (() -> a) -> a) ("sigopt: " ++ implode cp)
        (\ _ -> []);
    XML cp _ (XML_text _ : _) ->
      (error :: forall a. String -> (() -> a) -> a) ("sigopt: " ++ implode cp)
        (\ _ -> []);
  });

cpf_2_to_3_phase_1 :: Bool -> String -> String;
cpf_2_to_3_phase_1 ti s =
  (case doc_of_string (explode s) of {
    Inl err ->
      (error :: forall a. String -> (() -> a) -> a) (implode err) (\ _ -> s);
    Inr (XMLDOC _ x) ->
      let {
        x1 = remove_arg x;
      } in (case term_index_optional ti x1 of {
             (xa, tiTableOpt) ->
               (case rule_indices xa of {
                 (y, (riTable, m)) ->
                   (case flip_deletion m y of {
                     XML tag atts xs ->
                       xml_to_final_string
                         (XML tag atts
                           (xml "lookupTables" []
                              (tiTableOpt ++
                                [riTable] ++ signature_optional x1) :
                             xs));
                   });
               });
           });
  });

}
