module Groth where

open import Basics
open import Bwd
open import Thin

module _ {X : Set} where

  -- covering symmetry
  /u\-sym : forall {de ga xi : Bwd X}
             {th : de <= ga}
             {ph : xi <= ga}
          -> th /u\ ph
          -> ph /u\ th
  /u\-sym [] = []                          -- empty is symmetric
  /u\-sym (u -^, x) = /u\-sym u -,^ x      -- left-skip/right-keep -> left-keep/right-skip
  /u\-sym (u -,^ x) = /u\-sym u -^, x      -- left-keep/right-skip -> left-skip/right-keep
  /u\-sym (u -,  x) = /u\-sym u -,  x      -- both-keep is symmetric

  -- coverings are unique
  /u\-unique : forall {de ga xi : Bwd X}
               {th : de <= ga}
               {ph : xi <= ga}
            -> (u v : th /u\ ph)
            -> u ~ v
  /u\-unique [] [] = r~
  /u\-unique (u -^, x) (v -^, .x) with r~ <- /u\-unique u v = r~
  /u\-unique (u -,^ x) (v -,^ .x) with r~ <- /u\-unique u v = r~
  /u\-unique (u -,  x) (v -, .x)  with r~ <- /u\-unique u v = r~

  -- @wenkokke has figured this out
  cop2 : forall {de om xi : Bwd X}
         (th : de <= om)
         (ph : xi <= om)
      -> Cop th ph

  cop2 th ph = cop th ph .fst

  -- cannonical grothendieck covering transitivity for left-skip/right-keep
  -- induction on both inner covering and spine covering
  -- this is so I can normalise cop2 before implementing cov-groth
  cov-groth-r-can : forall {ga0 ga1 gal gar gasi : Bwd X}
                  {ph0 : ga0 <= gal}{ph1 : ga1 <= gal}
                  {thl : gal <= gasi}{thr : gar <= gasi}
                  {ps0 : ga0 <= gasi}{ps1 : ga1 <= gasi}
               -> ph0 /u\ ph1                                  -- inner covering
               -> thl /u\ thr                                  -- spine covering
               -> [ ph0 -< thl ]~ ps0                          -- triangle: ph0 . thl = ps0
               -> [ ph1 -< thl ]~ ps1                          -- triangle: ph1 . thl = ps1
               -> ps0 /u\ (cop2 ps1 thr) .fst .uuth            -- ps0 covers against the union of ps1 with thr

  cov-groth-r-can [] [] [] [] = []

  cov-groth-r-can rec (c_sp -^, x) (v0 -^ .x) (w0 -^ .x) =
    cov-groth-r-can rec c_sp v0 w0 -^, x

  cov-groth-r-can (rec -,^ .x) (c_sp -,^ x) (v0 -, .x) (w0 -^, .x) =
    cov-groth-r-can rec c_sp v0 w0 -,^ x

  cov-groth-r-can (rec -^, .x) (c_sp -,^ x) (v0 -^, .x) (w0 -, .x) =
    cov-groth-r-can rec c_sp v0 w0 -^, x

  cov-groth-r-can (rec -, .x) (c_sp -,^ x) (v0 -, .x) (w0 -, .x) =
    cov-groth-r-can rec c_sp v0 w0 -, x

  cov-groth-r-can (rec -,^ .x) (c_sp -, x) (v0 -, .x) (w0 -^, .x) =
    cov-groth-r-can rec c_sp v0 w0 -, x

  cov-groth-r-can (rec -^, .x) (c_sp -, x) (v0 -^, .x) (w0 -, .x) =
    cov-groth-r-can rec c_sp v0 w0 -^, x

  cov-groth-r-can (rec -, .x) (c_sp -, x) (v0 -, .x) (w0 -, .x) =
    cov-groth-r-can rec c_sp v0 w0 -, x

  -- apply cov-groth-r-can to an arbitrary Cop _ _
  cov-groth-r : forall {ga0 ga1 gal gar gasi : Bwd X}
              {ph0 : ga0 <= gal}  {ph1 : ga1 <= gal}
              {thl : gal <= gasi} {thr : gar <= gasi}
              {ps0 : ga0 <= gasi} {ps1 : ga1 <= gasi}
           -> ph0 /u\ ph1 -> thl /u\ thr
           -> [ ph0 -< thl ]~ ps0 -> [ ph1 -< thl ]~ ps1
           -> (c : Cop ps1 thr)
           -> ps0 /u\ c .fst .uuth
  cov-groth-r rec c_sp v0 w0 c
    with r~ <- unique (cop _ _) {c} {cop2 _ _}
       = cov-groth-r-can rec c_sp v0 w0

  -- cannonical transitivity for both-keep
  -- similar to cov-groth-r, but uses /u\ composed with cop2 on both sides
  cov-groth-both-can : forall {ga0 ga1 gal gar gasi : Bwd X}
                       {ph0 : ga0 <= gal}  {ph1 : ga1 <= gal}
                       {thl : gal <= gasi} {thr : gar <= gasi}
                       {ps0 : ga0 <= gasi} {ps1 : ga1 <= gasi}
                    -> ph0 /u\ ph1
                    -> thl /u\ thr
                    -> [ ph0 -< thl ]~ ps0
                    -> [ ph1 -< thl ]~ ps1
                    -> (cop2 ps0 thr) .fst .uuth /u\ (cop2 ps1 thr) .fst .uuth

  cov-groth-both-can [] [] [] [] = []

  cov-groth-both-can rec (c_sp -^, x) (v0 -^ .x) (w0 -^ .x) =
    cov-groth-both-can rec c_sp v0 w0 -, x

  cov-groth-both-can (rec -,^ .x) (c_sp -,^ x) (v0 -, .x) (w0 -^, .x) =
    cov-groth-both-can rec c_sp v0 w0 -,^ x

  cov-groth-both-can (rec -^, .x) (c_sp -,^ x) (v0 -^, .x) (w0 -, .x) =
    cov-groth-both-can rec c_sp v0 w0 -^, x

  cov-groth-both-can (rec -, .x) (c_sp -,^ x) (v0 -, .x) (w0 -, .x) =
    cov-groth-both-can rec c_sp v0 w0 -, x

  cov-groth-both-can (rec -,^ .x) (c_sp -, x) (v0 -, .x) (w0 -^, .x) =
    cov-groth-both-can rec c_sp v0 w0 -, x
  cov-groth-both-can (rec -^, .x) (c_sp -, x) (v0 -^, .x) (w0 -, .x) =
    cov-groth-both-can rec c_sp v0 w0 -, x
  cov-groth-both-can (rec -, .x) (c_sp -, x) (v0 -, .x) (w0 -, .x) =
    cov-groth-both-can rec c_sp v0 w0 -, x

  -- apply cov-groth-both-can to an arbitrary Cop _ _
  cov-groth-both : forall {ga0 ga1 gal gar gasi : Bwd X}
                   {ph0 : ga0 <= gal}  {ph1 : ga1 <= gal}
                   {thl : gal <= gasi} {thr : gar <= gasi}
                   {ps0 : ga0 <= gasi} {ps1 : ga1 <= gasi}
                -> ph0 /u\ ph1 -> thl /u\ thr
                -> [ ph0 -< thl ]~ ps0 -> [ ph1 -< thl ]~ ps1
                -> (c0 : Cop ps0 thr)(c1 : Cop ps1 thr)
                -> c0 .fst .uuth /u\ c1 .fst .uuth
  cov-groth-both rec c_sp v0 w0 c0 c1
    with r~ <- unique (cop _ _) {c0} {cop2 _ _}  -- normalise c0 to cop2 ps0 thr
       | r~ <- unique (cop _ _) {c1} {cop2 _ _}  -- normalise c1 to cop2 ps1 thr
       = cov-groth-both-can rec c_sp v0 w0


-- roof theorem via grothendieck transitivity

open import Tm

module _ {X : Set} (C : Sort X -> X -> Set) where

  open TM C

  roof-groth : forall {be0 be1 de al : Bwd X}
               {th0 : be0 <= al}{th1 : be1 <= al}
               {sg : de |= al}
               {br0@(ep0 , ta0 , ph0) : <: _|= be0 :* _<= de :>}
            -> (_ , th0 , sg) %% br0
            -> th0 /u\ th1
            -> {br1@(ep1 , ta1 , ph1) : <: _|= be1 :* _<= de :>}
            -> (_ , th1 , sg) %% br1
            -> ph0 /u\ ph1
  -- base case
  roof-groth [] [] [] = []

  -- case left-skip/right-keep: apply cov-groth-r to roof-groth
  roof-groth (naw s0 u0 t (_ , v0)) (u -^, x) (aye s1 _ _ (_ , w0) c) =
   cov-groth-r (roof-groth s0 u s1) u0 v0 w0 c

  -- case left-keep/right-skip: apply cov-groth-r to roof-groth,
  -- but use /u\-sym to get away with only having the right version
  roof-groth (aye s0 u0 _ (_ , v0) c) (u -,^ x) (naw s1 _ _ (_ , w0)) =
    /u\-sym (cov-groth-r (/u\-sym (roof-groth s0 u s1)) u0 w0 v0 c)

  -- case both-keep: apply cov-groth-both to roof-groth
  roof-groth (aye s0 u0 _ (_ , v0) c0) (u -, x) (aye s1 _ _ (_ , w0) c1) =
    cov-groth-both (roof-groth s0 u s1) u0 v0 w0 c0 c1

  -- roof is equivalent to roof-groth
  -- use uniqueness to say that, if a covering is unique,
  -- therefore roof and roof-groth must agree
  roof-equiv : forall {be0 be1 de al : Bwd X}
               {th0 : be0 <= al}
               {th1 : be1 <= al}{sg : de |= al}
               {br0@(ep0 , ta0 , ph0) : <: _|= be0 :* _<= de :>}
               (s0 : (_ , th0 , sg) %% br0)
               (u : th0 /u\ th1)
               {br1@(ep1 , ta1 , ph1) : <: _|= be1 :* _<= de :>}
               (s1 : (_ , th1 , sg) %% br1)
            -> roof s0 u s1 ~ roof-groth s0 u s1
  roof-equiv s0 u s1 = /u\-unique _ _
