import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homeomorph.Lemmas



set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M76.PhaseCovering

variable {ι Y : Type*} {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y]

theorem isLocalHomeomorph_sigma (g : ∀ i, C(X i, Y))
    (hg : ∀ i, IsLocalHomeomorph (g i)) : IsLocalHomeomorph (ContinuousMap.sigma g) := by
  rintro ⟨i, x⟩
  have hcomp : IsLocalHomeomorphOn ((ContinuousMap.sigma g) ∘ Sigma.mk i) univ :=
    (hg i).isLocalHomeomorphOn
  have hmk : IsLocalHomeomorphOn (@Sigma.mk ι X i) univ :=
    Topology.IsOpenEmbedding.sigmaMk.isLocalHomeomorph.isLocalHomeomorphOn
  exact hcomp.of_comp_right hmk _ ⟨x, mem_univ x, rfl⟩

theorem isCoveringMap_finite_sigma [Finite ι] [∀ i, CompactSpace (X i)]
    [∀ i, T2Space (X i)] [T2Space Y]
    (g : ∀ i, C(X i, Y)) (hg : ∀ i, IsCoveringMap (g i)) :
    IsCoveringMap (ContinuousMap.sigma g) :=
  isLocalHomeomorph_iff_isCoveringMap.mp
    (isLocalHomeomorph_sigma g fun i => (hg i).isLocalHomeomorph)


def sigmaHomotopy {f g : ∀ i, C(X i, Y)} (H : ∀ i, (f i).Homotopy (g i)) :
    (ContinuousMap.sigma f).Homotopy (ContinuousMap.sigma g) where
  toFun z := H z.2.1 (z.1, z.2.2)
  continuous_toFun := by
    have hc : Continuous (fun z : Σ i, X i × unitInterval => H z.1 (z.2.2, z.2.1)) :=
      continuous_sigma fun i => (H i).continuous.comp (continuous_snd.prodMk continuous_fst)
    exact hc.comp (Homeomorph.sigmaProdDistrib.continuous.comp
      (continuous_snd.prodMk continuous_fst))
  map_zero_left z := (H z.1).apply_zero z.2
  map_one_left z := (H z.1).apply_one z.2

@[simp] theorem sigmaHomotopy_apply {f g : ∀ i, C(X i, Y)}
    (H : ∀ i, (f i).Homotopy (g i)) (t : unitInterval) (i : ι) (x : X i) :
    sigmaHomotopy H (t, ⟨i, x⟩) = H i (t, x) := rfl

end PoincareConjecture.M76.PhaseCovering
