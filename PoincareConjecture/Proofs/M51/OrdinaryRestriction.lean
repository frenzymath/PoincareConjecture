import PoincareConjecture.Definitions.Ch03.RicciFlow

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51Ordinary

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J K : Set ℝ}

def restrict (F : RicciFlow n M J) (hKJ : K ⊆ J)
    (hK : K.OrdConnected) (hne : K.Nontrivial) : RicciFlow n M K where
  metric := F.metric
  connection := F.connection
  interval := hK
  nontrivial := hne
  smooth := F.smooth.mono (Set.prod_mono hKJ (Subset.refl _))
  equation t ht x v w := (F.equation t (hKJ ht) x v w).mono hKJ

@[simp] theorem restrict_metric (F : RicciFlow n M J) (hKJ : K ⊆ J)
    (hK : K.OrdConnected) (hne : K.Nontrivial) (t : ℝ) :
    (restrict F hKJ hK hne).metric t = F.metric t := rfl

@[simp] theorem restrict_connection (F : RicciFlow n M J) (hKJ : K ⊆ J)
    (hK : K.OrdConnected) (hne : K.Nontrivial) (t : ℝ) :
    (restrict F hKJ hK hne).connection t = F.connection t := rfl

end PoincareConjecture.M51Ordinary
