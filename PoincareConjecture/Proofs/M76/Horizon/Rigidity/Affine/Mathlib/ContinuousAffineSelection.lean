import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.HyperplaneSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProduct
import Mathlib.Topology.Connected.TotallyDisconnected












set_option autoImplicit false

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem Convex.eqOn_zero_or_affine_of_selection_nonpos
    {C : Set E} (hC : Convex ℝ C) (A : E →ᴬ[ℝ] ℝ)
    (hA : ∀ x ∈ C, A x ≤ 0) {g : E → ℝ} (hg : ContinuousOn g C)
    (hselect : ∀ x ∈ C, g x = 0 ∨ g x = A x) :
    EqOn g (fun _ => 0) C ∨ EqOn g A C := by
  classical
  by_cases hne : ∃ x ∈ C, A x < 0
  · obtain ⟨x, hx, hxneg⟩ := hne
    let U := C ∩ {y | A y < 0}
    have hU : Convex ℝ U := hC.inter ((convex_Iio (0 : ℝ)).affine_preimage A.toAffineMap)
    have hratio : ContinuousOn (fun y => g y / A y) U :=
      (hg.mono inter_subset_left).div A.continuous.continuousOn
        (fun y hy => ne_of_lt hy.2)
    have hvalues : MapsTo (fun y => g y / A y) U ({0, 1} : Set ℝ) := by
      intro y hy
      rcases hselect y hy.1 with h | h
      · simp [h]
      · simp [h, ne_of_lt (show A y < 0 from hy.2)]
    have hconstant (y : E) (hy : y ∈ U) : g y / A y = g x / A x :=
      hU.isPreconnected.constant_of_mapsTo
        (((finite_singleton (1 : ℝ)).insert 0).isDiscrete) hratio hvalues hy ⟨hx, hxneg⟩
    rcases hselect x hx with hxzero | hxaff
    · left
      intro y hy
      by_cases hAy : A y = 0
      · exact (hselect y hy).elim id (fun h => h.trans hAy)
      · have h := hconstant y ⟨hy, lt_of_le_of_ne (hA y hy) hAy⟩
        rw [hxzero, zero_div] at h
        exact (div_eq_zero_iff.mp h).resolve_right hAy
    · right
      intro y hy
      by_cases hAy : A y = 0
      · exact (hselect y hy).elim (fun h => h.trans hAy.symm) id
      · have h := hconstant y ⟨hy, lt_of_le_of_ne (hA y hy) hAy⟩
        rw [hxaff, div_self (ne_of_lt hxneg)] at h
        exact (div_eq_one_iff_eq hAy).mp h
  · left
    intro x hx
    have hzero : A x = 0 := le_antisymm (hA x hx) (not_lt.mp (fun h => hne ⟨x, hx, h⟩))
    exact (hselect x hx).elim id (fun h => h.trans hzero)



theorem Convex.eqOn_zero_or_affine_of_selection
    {C : Set E} (hC : Convex ℝ C) (A : E →ᴬ[ℝ] ℝ)
    (hA : (∀ x ∈ C, A x ≤ 0) ∨ (∀ x ∈ C, 0 ≤ A x))
    {g : E → ℝ} (hg : ContinuousOn g C)
    (hselect : ∀ x ∈ C, g x = 0 ∨ g x = A x) :
    EqOn g (fun _ => 0) C ∨ EqOn g A C := by
  rcases hA with hA | hA
  · exact Convex.eqOn_zero_or_affine_of_selection_nonpos hC A hA hg hselect
  · have h := Convex.eqOn_zero_or_affine_of_selection_nonpos hC (-A)
      (fun x hx => neg_nonpos.mpr (hA x hx)) hg.neg (by
        intro x hx
        exact (hselect x hx).imp (fun h => by simp [h]) (fun h => by simp [h]))
    exact h.imp (fun h x hx => neg_eq_zero.mp (h hx))
      (fun h x hx => neg_injective (h hx))

namespace Geometry



theorem FinitePiecewiseAffineOn.continuous_selection_zero
    {f g : E → ℝ} {C : Set E} (hf : FinitePiecewiseAffineOn f C)
    (hg : ContinuousOn g C) (hselect : ∀ x ∈ C, g x = 0 ∨ g x = f x) :
    FinitePiecewiseAffineOn g C := by
  classical
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  choose A hA using fun t : K.faces => hfaces t.val t.property
  let : Fintype K.faces := hK.fintype
  let cuts : Finset (E →ᵃ[ℝ] ℝ) := Finset.univ.image (fun t : K.faces => (A t).toAffineMap)
  let N := hK.toFinset.sup Finset.card
  have hN (t : Finset E) (ht : t ∈ K.faces) : t.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr ht)).trans (Nat.le_succ N)
  obtain ⟨L, hL, hLK, _, hcuts⟩ := K.exists_subdivision_respectsAffineHyperplanes hK hN cuts
  refine ⟨L, hL, hLK.space_eq, ?_⟩
  intro s hs
  obtain ⟨t, ht, hst⟩ := hLK.face_subset s hs
  let tK : K.faces := ⟨t, ht⟩
  have hcut : (A tK).toAffineMap ∈ cuts := Finset.mem_image.mpr ⟨tK, Finset.mem_univ _, rfl⟩
  have hsK := hst.trans (K.convexHull_subset_space ht)
  have hsel : ∀ x ∈ convexHull ℝ (s : Set E), g x = 0 ∨ g x = A tK x := by
    intro x hx
    exact (hselect x (hsK hx)).imp id (fun h => h.trans (hA tK (hst hx)))
  rcases Convex.eqOn_zero_or_affine_of_selection (convex_convexHull ℝ (s : Set E))
    (A tK) (hcuts _ hcut s hs) (hg.mono hsK) hsel with hz | ha
  · exact ⟨ContinuousAffineMap.const ℝ E 0, hz⟩
  · exact ⟨A tK, ha⟩



theorem FinitePiecewiseAffineOn.continuous_selection [FiniteDimensional ℝ E]
    {f₀ f₁ g : E → ℝ} {C : Set E} (h₀ : FinitePiecewiseAffineOn f₀ C)
    (h₁ : FinitePiecewiseAffineOn f₁ C) (hg : ContinuousOn g C)
    (hselect : ∀ x ∈ C, g x = f₀ x ∨ g x = f₁ x) :
    FinitePiecewiseAffineOn g C := by
  have hd : FinitePiecewiseAffineOn (fun x => g x - f₀ x) C :=
    (h₁.sub h₀).continuous_selection_zero (hg.sub h₀.continuousOn) (by
      intro x hx
      exact (hselect x hx).imp (fun h => by simp [h]) (fun h => by rw [h]))
  exact (hd.add h₀).congr (fun x _ => sub_add_cancel (g x) (f₀ x))



theorem FinitePiecewiseAffineOn.continuous_selection_pi
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    {f₀ f₁ g : E → (ι → ℝ)} {C : Set E} (h₀ : FinitePiecewiseAffineOn f₀ C)
    (h₁ : FinitePiecewiseAffineOn f₁ C) (hg : ContinuousOn g C)
    (hselect : ∀ x ∈ C, g x = f₀ x ∨ g x = f₁ x) :
    FinitePiecewiseAffineOn g C := by
  obtain ⟨K, hK, hKC, hfK⟩ := h₀
  have h₀ : FinitePiecewiseAffineOn f₀ C := ⟨K, hK, hKC, hfK⟩
  have hcoords (i : ι) : FinitePiecewiseAffineOn (fun x => g x i) K.space := by
    rw [hKC]
    let p : (ι → ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj i).toContinuousAffineMap
    exact (h₀.postcomp p).continuous_selection (h₁.postcomp p)
      ((continuous_apply i).comp_continuousOn hg) (fun x hx =>
        (hselect x hx).imp (congrFun · i) (congrFun · i))
  obtain ⟨L, hL, hLK, hfaces⟩ := FinitePiecewiseAffineOn.pi_on_complex K hK hcoords
  exact ⟨L, hL, hLK.trans hKC, hfaces⟩

end Geometry
