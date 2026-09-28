import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.Trees
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.MorseChart
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.MorseReduction

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereMorseReduction
open Poincare.Geometry.Euclidean
open PlaneArcs.Terminal.Reflection

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3}

def reflectedOriginal (M : SphereMorseReduction f) : S2 → E3 :=
  fun q => M.D.symm (heightReflection (mem_sphere_zero_iff_norm.mp M.v.property) (M.D (f q)))

@[simp] theorem reflectedOriginal_initial (M : SphereMorseReduction f) (q : S2) :
    M.D (M.reflectedOriginal q) =
      heightReflection (mem_sphere_zero_iff_norm.mp M.v.property) (M.D (f q)) :=
  M.D.apply_symm_apply _

theorem exists_reflected (M : SphereMorseReduction f) :
    ∃ R : SphereMorseReduction M.reflectedOriginal,
      R.v = M.v ∧ R.D = M.D ∧ R.cuts = M.cuts.image Neg.neg ∧
      (∀ q, R.D (M.reflectedOriginal q) =
        heightReflection (mem_sphere_zero_iff_norm.mp M.v.property) (M.D (f q))) ∧
      ∀ g ∈ M.tree.leaves,
        heightReflection (mem_sphere_zero_iff_norm.mp M.v.property) ∘ g ∈ R.tree.leaves := by
  classical
  let hv : ‖(M.v : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp M.v.property
  let J := heightReflection hv
  let H : S2 → Real := fun q => inner Real (M.v : E3) (M.D (f q))
  let HR : S2 → Real := fun q => inner Real (M.v : E3) (M.D (M.reflectedOriginal q))
  have hi : (fun q => M.D (M.reflectedOriginal q)) = J ∘ (fun q => M.D (f q)) := by
    funext q
    exact M.reflectedOriginal_initial q
  have hh (q) : HR q = -H q := by
    dsimp [HR, H]
    rw [M.reflectedOriginal_initial, inner_heightReflection]
  have hcrit (q) : mfderiv (𝓡 2) 𝓘(Real, Real) HR q = 0 ↔
      mfderiv (𝓡 2) 𝓘(Real, Real) H q = 0 := by
    rw [show HR = -H from funext hh, mfderiv_neg, neg_eq_zero]
  have hcritical : {q | mfderiv (𝓡 2) 𝓘(Real, Real) HR q = 0} =
      {q | mfderiv (𝓡 2) 𝓘(Real, Real) H q = 0} := Set.ext hcrit
  have hvalues : HR '' {q | mfderiv (𝓡 2) 𝓘(Real, Real) HR q = 0} =
      Neg.neg '' (H '' {q | mfderiv (𝓡 2) 𝓘(Real, Real) H q = 0}) := by
    rw [hcritical, image_image]
    exact image_congr (fun q _ => hh q)
  have ht : ∃ T : SphereSurgeryTree M.v (M.cuts.image Neg.neg)
      (fun q => M.D (M.reflectedOriginal q)),
      T.Protects (HR '' {q | mfderiv (𝓡 2) 𝓘(Real, Real) HR q = 0}) ∧
      T.PreservesCaps ∧ ∀ g ∈ M.tree.leaves, J ∘ g ∈ T.leaves := by
    rw [hi, hvalues]
    exact ⟨M.tree.reflected hv, M.protects_critical_values.reflected hv,
      M.preserves_caps.reflected hv, fun _ hg => M.tree.reflected_mem_leaves hv hg⟩
  obtain ⟨T, hprotect, hcaps, hleaves⟩ := ht
  let R : SphereMorseReduction M.reflectedOriginal := {
    v := M.v
    D := M.D
    compact_support := M.compact_support
    embedding := by
      rw [hi]
      exact SphereSurgeryStep.sphere_embedding_postcompose J M.embedding
    finite_critical := hcritical ▸ M.finite_critical
    distinct_values := by
      intro p hp q hq heq
      exact M.distinct_values ((hcrit p).mp hp) ((hcrit q).mp hq)
        (neg_injective ((hh p).symm.trans (heq.trans (hh q))))
    coordinates := by
      intro p hp
      obtain ⟨e, σ, hσ, he0, hep, he, hei, hform⟩ := M.coordinates p ((hcrit p).mp hp)
      refine ⟨e, -σ, ?_, he0, hep, he, hei, ?_⟩
      · intro i
        rcases hσ i with hn | hp
        · exact Or.inr (by simp only [Pi.neg_apply, hn, neg_neg])
        · exact Or.inl (by simp only [Pi.neg_apply, hp])
      · intro x hx
        change HR (e x) = HR p + ∑ i : Fin 2, (-σ) i * x i ^ 2
        rw [hh, hh]
        change -(inner Real (M.v : E3) (M.D (f (e x)))) = _
        rw [hform x hx]
        simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_add_rev, H]
        ring
    cuts := M.cuts.image Neg.neg
    regular := by
      intro c hc q hq hzero
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
      apply M.regular k hk q _ ((hcrit q).mp hzero)
      exact neg_injective ((hh q).symm.trans hq)
    separates_critical := by
      intro p q hp hq hcomp
      apply M.separates_critical p q ((hcrit p).mp hp) ((hcrit q).mp hq)
      have hpout : HR p ∈ (↑(M.cuts.image Neg.neg) : Set Real)ᶜ := by
        intro hpm
        obtain ⟨k, hk, hkp⟩ := Finset.mem_image.mp hpm
        exact M.regular k hk p (neg_injective ((hh p).symm.trans hkp.symm))
          ((hcrit p).mp hp)
      have himage : Neg.neg '' (↑(M.cuts.image Neg.neg) : Set Real)ᶜ =
          (↑M.cuts : Set Real)ᶜ := by
        ext x
        simp only [mem_image, mem_compl_iff, Finset.mem_coe, Finset.mem_image]
        constructor
        · rintro ⟨y, hy, rfl⟩ hx
          exact hy ⟨-y, hx, neg_neg y⟩
        · intro hx
          refine ⟨-x, ?_, neg_neg x⟩
          rintro ⟨y, hy, heq⟩
          exact hx (neg_injective heq ▸ hy)
      have hm := continuous_neg.continuousOn.image_connectedComponentIn_subset hpout
        (mem_image_of_mem Neg.neg hcomp)
      rw [himage] at hm
      change -HR q ∈ connectedComponentIn (↑M.cuts : Set Real)ᶜ (-HR p) at hm
      rw [hh, hh, neg_neg, neg_neg] at hm
      exact hm
    tree := T
    protects_critical_values := hprotect
    preserves_caps := hcaps }
  exact ⟨R, rfl, rfl, rfl, M.reflectedOriginal_initial, hleaves⟩

end Poincare.Manifold.Schoenflies.SphereMorseReduction

end

end M38Schoenflies
