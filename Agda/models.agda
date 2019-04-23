{-# OPTIONS --without-K #-}

{- Our goal in this file is to observe some structure possessed by the
   universes of types, reflexive graphs, type families, and so on. Somewhat
   more precisely, we develop an imperfect structure of internal model of type
   theory, with enough ingredients to get some type theoretic developments off
   the ground.

   We begin with the basic structure of type dependency, with operations for
   context extension, weakening, substitution, and identity morphisms (the
   `variable rule'). Once this structure is implemented, we introduce the
   structure of usual type constructors Σ, Π, Id, the unit type, and ℕ. 

   The reason this is an `imperfect' notion of model structure is that
   in our internal model structure, we have identifications in the role of
   judgmental equalities. This leads to the usual coherence problem, which we
   do not attempt to solve. As we said before, our goal is merely to postulate
   enough equalities so that we can introduce and work with the type
   constructors. We then proceed to develop some examples.
-}

module models where

import Lecture15
open Lecture15 public

Contexts :
  ( l : Level) → UU (lsuc l)
Contexts l = UU l

Families :
  { l1 : Level} (l2 : Level) (ctx : Contexts l1) → UU (l1 ⊔ (lsuc l2))
Families l2 ctx = ctx → UU l2

Terms :
  { l1 l2 : Level} (l3 : Level)
  ( ctx : Contexts l1) (fam : Families l2 ctx) → UU (l1 ⊔ (l2 ⊔ (lsuc l3)))
Terms l3 ctx fam = (Γ : ctx) → (fam Γ) → UU l3

Context-Extensions :
  { l1 l2 : Level}
  ( ctx : Contexts l1) (fam : Families l2 ctx) → UU (l1 ⊔ l2)
Context-Extensions ctx fam = (Γ : ctx) → (fam Γ) → ctx

Family-Extensions :
  { l1 l2 : Level}
  ( ctx : Contexts l1) (fam : Families l2 ctx)
  ( ctx-ext : Context-Extensions ctx fam) → UU (l1 ⊔ l2)
Family-Extensions ctx fam ctx-ext =
  ( Γ : ctx) → (A : fam Γ) → (fam (ctx-ext Γ A)) → fam Γ
  
Model-Base :
  ( l1 l2 l3 : Level) → UU (lsuc l1 ⊔ (lsuc l2 ⊔ lsuc l3))
Model-Base l1 l2 l3 =
  Σ ( Contexts l1)
    ( λ ctx → Σ (Families l2 ctx)
      ( λ fam → Σ (Terms l3 ctx fam)
        ( λ tm → Σ (Context-Extensions ctx fam) (Family-Extensions ctx fam))))

Hom-Model-Base :
  { l1 l2 l3 l1' l2' l3' : Level} →
  Model-Base l1 l2 l3 → Model-Base l1' l2' l3' → UU _
Hom-Model-Base
  ( pair ctx (pair fam (pair tm (pair ctx-ext fam-ext))))
  ( pair ctx' (pair fam' (pair tm' (pair ctx-ext' fam-ext')))) =
   Σ ( ctx → ctx')
     ( λ h-ctx → Σ ((Γ : ctx) → (fam Γ) → (fam' (h-ctx Γ)))
       ( λ h-fam →
         Σ ((Γ : ctx) (A : fam Γ) → (tm Γ A) → tm' (h-ctx Γ) (h-fam Γ A))
         ( λ h-tm →
           Σ ( (Γ : ctx) (A : fam Γ) →
               Id
                 ( h-ctx (ctx-ext Γ A))
                 ( ctx-ext' (h-ctx Γ) (h-fam Γ A)))
             ( λ h-ctx-ext → (Γ : ctx) (A : fam Γ) (B : fam (ctx-ext Γ A)) →
               Id
                 ( h-fam Γ (fam-ext Γ A B))
                 ( fam-ext'
                   ( h-ctx Γ)
                   ( h-fam Γ A)
                   ( tr fam' (h-ctx-ext Γ A) (h-fam (ctx-ext Γ A) B)))))))

Assoc-Ctx-ext :
  { l1 l2 l3 : Level} (M : Model-Base l1 l2 l3) → UU (l1 ⊔ l2)
Assoc-Ctx-ext (pair ctx (pair fam (pair tm (pair ctx-ext fam-ext)))) =
  ( Γ : ctx) (A : fam Γ) (B : fam (ctx-ext Γ A)) →
    Id (ctx-ext (ctx-ext Γ A) B) (ctx-ext Γ (fam-ext Γ A B))

Slice-Model-Base :
  { l1 l2 l3 : Level} (M : Model-Base l1 l2 l3)
  ( assoc : Assoc-Ctx-ext M) →
  ( Γ : pr1 M) → Model-Base l2 l2 l3
Slice-Model-Base
  ( pair ctx (pair fam (pair tm (pair ctx-ext fam-ext)))) assoc Γ =
  pair (fam Γ)
    ( pair (λ A → fam (ctx-ext Γ A))
      ( pair (λ A B → tm (ctx-ext Γ A) B)
        ( pair (fam-ext Γ)
          ( λ A B C →
            fam-ext (ctx-ext Γ A) B (tr fam (inv (assoc Γ A B)) C)))))

Empty-context :
  { l1 l2 l3 : Level} (M : Model-Base l1 l2 l3) → UU l1
Empty-context M = pr1 M

Axiom-Empty-Context :
  { l1 l2 l3 : Level}
  (M : Model-Base l1 l2 l3) (empty-ctx : Empty-context M) → UU (l1 ⊔ l2)
Axiom-Empty-Context
  ( pair ctx (pair fam (pair tm (pair ctx-ext fam-ext)))) empty-ctx =
  is-equiv (ctx-ext empty-ctx)
