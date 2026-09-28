import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactClosedStrip
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "K2" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "I+" => Icc (0 : ℝ) 1

theorem exists_confined_disk_collar_of_finite_surface_product
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {D W O : Set X} {A S : Set E}
    (F : X → E) (g : E → X)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g A) (hgi : InjOn g A)
    (f : E × ℝ → E) (hf : FinitePiecewiseAffineOn f (S ×ˢ I))
    (hfi : InjOn f (S ×ˢ I)) (hfA : MapsTo f (S ×ˢ I) A)
    (hf0 : ∀ x ∈ S, f (x, 0) = x)
    (hfW : ∀ z ∈ S ×ˢ I, g (f z) ∈ W)
    (hfD : ∀ z ∈ S ×ˢ I, g (f z) ∈ D ↔ 0 ≤ z.2)
    (hffD : ∀ z ∈ S ×ˢ I, g (f z) ∈ frontier D ↔ z.2 = 0)
    (hffW : ∀ z ∈ S ×ˢ I, g (f z) ∈ frontier W ↔ g z.1 ∈ frontier W)
    (j : V2 → X) (hj : PolyhedralPLInCharts e j K2) (hji : InjOn j K2)
    (hjS : MapsTo (F ∘ j) K2 S) (hgj : ∀ z ∈ K2, g (F (j z)) = j z)
    (hO : IsOpen O) (hjO : j '' K2 ⊆ O) :
    ∃ (δ : ℝ) (k : V2 × ℝ → X), 0 < δ ∧ δ ≤ 1 / 2 ∧
      (∀ z, k z = g (f (F (j z.1), δ * z.2))) ∧
      PolyhedralPLInCharts e k (K2 ×ˢ I+) ∧ InjOn k (K2 ×ˢ I+) ∧
      MapsTo k (K2 ×ˢ I+) (D ∩ W ∩ O) ∧
      (∀ z ∈ K2, k (z, 0) = j z) ∧
      (∀ z ∈ K2 ×ˢ I+, k z ∈ frontier D ↔ z.2 = 0) ∧
      ∀ z ∈ K2 ×ˢ I+, k z ∈ frontier W ↔ j z.1 ∈ frontier W := by
  classical
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  have hjK : PolyhedralPLInCharts e j K.space := hKs.symm ▸ hj
  let b : V2 → E := F ∘ j
  have hb : FinitePiecewiseAffineOn b K2 :=
    hKs ▸ hjK.finitePiecewiseAffineOn_comp K hK hF
  have hbi : InjOn b K2 := by
    intro x hx y hy he
    apply hji hx hy
    exact (hgj x hx).symm.trans ((congrArg g he).trans (hgj y hy))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) I :=
    ⟨J, hJ, hJs, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  let q : V2 × ℝ → E := f ∘ Prod.map b id
  have hparam : MapsTo (Prod.map b (id : ℝ → ℝ)) (K2 ×ˢ I) (S ×ˢ I) :=
    fun _ hx ↦ ⟨hjS hx.1, hx.2⟩
  have hq : FinitePiecewiseAffineOn q (K2 ×ˢ I) := hf.comp (hb.prodMap hid) hparam
  have hqA : MapsTo q (K2 ×ˢ I) A := fun _ hx ↦ hfA (hparam hx)
  let P : V2 × ℝ → X := g ∘ q
  have hP : PolyhedralPLInCharts e P (K2 ×ˢ I) := by
    obtain ⟨L, hL, hLs, hfaces⟩ := hq
    rw [← hLs]
    exact hg.comp_finitePiecewiseAffineOn L hL ⟨L, hL, rfl, hfaces⟩
      (fun _ hx ↦ hqA (hLs.subset hx))
  have hPi : InjOn P (K2 ×ˢ I) := by
    intro x hx y hy he
    have hxy := hfi (hparam hx) (hparam hy) (hgi (hqA hx) (hqA hy) he)
    apply Prod.ext
    · exact hbi hx.1 hy.1 (congrArg (fun z : E × ℝ ↦ z.1) hxy)
    · exact congrArg (fun z : E × ℝ ↦ z.2) hxy
  have hP0 (z : V2) (hz : z ∈ K2) : P (z, 0) = j z := by
    change g (f (b z, 0)) = j z
    rw [hf0 (b z) (hjS hz)]
    exact hgj z hz
  let P0 : K2 × I → X := fun z ↦ P ((z.1 : V2), (z.2 : ℝ))
  have hP0c : Continuous P0 :=
    hP.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun z ↦ ⟨z.1.property, z.2.property⟩)
  let : CompactSpace K2 := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : V2) 1)
  obtain ⟨δ, hδ, hδsmall, hthin⟩ := hP0c.exists_closed_strip_subset hO (by
    intro z
    change P ((z : V2), 0) ∈ O
    rw [hP0 z z.property]
    exact hjO ⟨z, z.property, rfl⟩)
  let a : ℝ →ᴬ[ℝ] ℝ := δ • ContinuousAffineMap.id ℝ ℝ
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have ha : FinitePiecewiseAffineOn a I+ := ⟨L, hL, hLs, L.affineOnFaces_affine a⟩
  have hId : FinitePiecewiseAffineOn (id : V2 → V2) K2 :=
    ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V2)⟩
  have haI (t : ℝ) (ht : t ∈ I+) : δ * t ∈ I := by
    constructor <;> nlinarith [ht.1, ht.2]
  let r : V2 × ℝ → V2 × ℝ := Prod.map id a
  have hr : FinitePiecewiseAffineOn r (K2 ×ˢ I+) := hId.prodMap ha
  have hrI : MapsTo r (K2 ×ˢ I+) (K2 ×ˢ I) := fun x hx ↦ ⟨hx.1, haI x.2 hx.2⟩
  let k : V2 × ℝ → X := P ∘ r
  have hk : PolyhedralPLInCharts e k (K2 ×ˢ I+) := by
    obtain ⟨M, hM, hMs, hfaces⟩ := hr
    rw [← hMs]
    exact hP.comp_finitePiecewiseAffineOn M hM ⟨M, hM, rfl, hfaces⟩
      (fun _ hx ↦ hrI (hMs.subset hx))
  have hinput (x : V2 × ℝ) (hx : x ∈ K2 ×ˢ I+) :
      (F (j x.1), δ * x.2) ∈ S ×ˢ I := ⟨hjS hx.1, haI x.2 hx.2⟩
  refine ⟨δ, k, hδ, hδsmall, fun _ ↦ rfl, hk, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy he
    have hxy := hPi (hrI hx) (hrI hy) he
    apply Prod.ext
    · simpa only [r, Prod.map_fst, id_eq] using congrArg (fun z : V2 × ℝ ↦ z.1) hxy
    · exact mul_left_cancel₀ hδ.ne' (congrArg (fun z : V2 × ℝ ↦ z.2) hxy)
  · intro x hx
    refine ⟨⟨(hfD _ (hinput x hx)).mpr (mul_nonneg hδ.le hx.2.1),
      hfW _ (hinput x hx)⟩, ?_⟩
    exact hthin ⟨x.1, hx.1⟩ ⟨δ * x.2, haI x.2 hx.2⟩ (by
      rw [abs_of_nonneg (mul_nonneg hδ.le hx.2.1)]
      exact mul_le_of_le_one_right hδ.le hx.2.2)
  · intro z hz
    change P (z, δ * 0) = j z
    simpa using hP0 z hz
  · intro z hz
    change g (f (F (j z.1), δ * z.2)) ∈ frontier D ↔ z.2 = 0
    rw [hffD _ (hinput z hz), mul_eq_zero]
    exact or_iff_right hδ.ne'
  · intro z hz
    change g (f (F (j z.1), δ * z.2)) ∈ frontier W ↔ j z.1 ∈ frontier W
    rw [hffW _ (hinput z hz), hgj z.1 hz.1]

end PoincareConjecture.M76
