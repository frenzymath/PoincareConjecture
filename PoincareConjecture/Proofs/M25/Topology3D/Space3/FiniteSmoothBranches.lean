import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularFibers

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
variable [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
variable [CompactSpace M] [T2Space M] [T2Space N]

theorem exists_finite_smooth_inverse_branches
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f) (y : N)
    (hregular : ∀ x, f x = y →
      Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x)) :
    (f ⁻¹' {y}).Finite ∧
      ∃ (W : Set N) (g : (f ⁻¹' {y}) → N → M), IsOpen W ∧ y ∈ W ∧
        (∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (g i) W) ∧
        (∀ i z, z ∈ W → f (g i z) = z) ∧
        (∀ x, f x ∈ W → ∃ i, g i (f x) = x) ∧
        (∀ z ∈ W, Function.Injective (fun i => g i z)) ∧
        ∀ i, g i y = (i : M) := by
  classical
  have hfinite := finite_regular_fiber f hf y hregular
  let : Finite (f ⁻¹' {y}) := hfinite
  choose e he hem hei using fun i : f ⁻¹' {y} =>
    exists_smooth_manifold_local_inverse f hf i (hregular i i.2)
  obtain ⟨O, hO, hdisj⟩ := hfinite.t2_separation
  let V : (f ⁻¹' {y}) → Set M := fun i => (e i).source ∩ O i
  have hV (i : f ⁻¹' {y}) : IsOpen (V i) := (e i).open_source.inter (hO i).2
  have hiV (i : f ⁻¹' {y}) : (i : M) ∈ V i := ⟨he i, (hO i).1⟩
  have himage (i : f ⁻¹' {y}) : IsOpen (f '' V i) := by
    rw [← hem i]
    exact (e i).isOpen_image_of_subset_source (hV i) inter_subset_left
  let W0 : Set N := (f '' (⋃ i, V i)ᶜ)ᶜ
  have hW0 : IsOpen W0 :=
    (hf.continuous.isClosedMap _ (isOpen_iUnion hV).isClosed_compl).isOpen_compl
  have hyW0 : y ∈ W0 := by
    rintro ⟨x, hx, hxy⟩
    exact hx (mem_iUnion_of_mem (⟨x, hxy⟩ : f ⁻¹' {y}) (hiV ⟨x, hxy⟩))
  let W := W0 ∩ ⋂ i, f '' V i
  have hW : IsOpen W := hW0.inter (isOpen_iInter_of_finite himage)
  have hyW : y ∈ W :=
    ⟨hyW0, mem_iInter.mpr (fun i => ⟨i, hiV i, i.2⟩)⟩
  have htarget (i : f ⁻¹' {y}) {z : N} (hz : z ∈ W) : z ∈ (e i).target := by
    obtain ⟨x, hx, hfx⟩ := mem_iInter.mp hz.2 i
    rw [← hfx, ← hem i]
    exact (e i).map_source hx.1
  have hinverse (i : f ⁻¹' {y}) {z : N} (hz : z ∈ W) : (e i).symm z ∈ V i := by
    obtain ⟨x, hx, hfx⟩ := mem_iInter.mp hz.2 i
    rw [← hfx, ← hem i, (e i).left_inv hx.1]
    exact hx
  refine ⟨hfinite, W, fun i => (e i).symm, hW, hyW, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hei i).mono (fun _ hz => htarget i hz)
  · intro i z hz
    exact (congrFun (hem i) ((e i).symm z)).symm.trans
      ((e i).right_inv (htarget i hz))
  · intro x hx
    have hxV : x ∈ ⋃ i, V i := by
      by_contra h
      exact hx.1 ⟨x, h, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxV
    refine ⟨i, ?_⟩
    exact (congrArg (e i).symm (congrFun (hem i) x).symm).trans ((e i).left_inv hi.1)
  · intro z hz i j hij
    by_contra hne
    have hne' : (i : M) ≠ (j : M) := fun h => hne (Subtype.ext h)
    have hij' : (e i).symm z = (e j).symm z := hij
    apply Set.disjoint_left.mp (hdisj i.2 j.2 hne') (hinverse i hz).2
    rw [hij']
    exact (hinverse j hz).2
  · intro i
    have hiy : f i = y := i.2
    exact (congrArg (e i).symm ((congrFun (hem i) i).trans hiy).symm).trans
      ((e i).left_inv (he i))

end PoincareConjecture.M25.Topology3D
