import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLClosedExtension
import PoincareConjecture.Proofs.M76.Mathlib.ClosedBallIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductTriangulation









set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem alexanderFamily_joint_finitePL (G : E ≃ₜ E) {C : Set E}
    (hG : FinitePiecewiseAffineOn (G : E → E) C)
    {ι : Type*} [Finite ι] (L : ι → E →ₗ[ℝ] ℝ)
    (hrep : C = {x | ∀ i, L i x ≤ 1})
    (hfix : ∀ i x, 1 ≤ L i x → G x = x)
    (J : SimplicialComplex ℝ (ℝ × E)) (hJ : J.faces.Finite)
    (htime : ∀ p ∈ J.space, p.1 ∈ Icc (0 : ℝ) 1) :
    FinitePiecewiseAffineOn (fun p : ℝ × E => G.alexanderFamily p.1 p.2) J.space := by
  classical
  let A : E →ᴬ[ℝ] ℝ × E :=
    (ContinuousAffineMap.const ℝ E 1).prod (ContinuousAffineMap.id ℝ E)
  let B : Set (ℝ × E) := A '' C
  let H : Set (ℝ × E) := convexJoin ℝ {0} B
  let T : ℝ × E → E := fun p => G.alexanderFamily p.1 p.2
  have hG' := hG
  obtain ⟨K, hK, hKs, _⟩ := hG'
  have hA : FinitePiecewiseAffineOn A C := by
    rw [← hKs]
    exact (K.affineOnFaces_affine A).finitePiecewiseAffineOn hK
  have hproj : FinitePiecewiseAffineOn (Prod.snd : ℝ × E → E) B :=
    hA.inverse (fun _ _ => rfl)
  have hbase : FinitePiecewiseAffineOn (fun p : ℝ × E => G p.2) B :=
    hG.comp hproj (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  have hB : B.Nonempty := by
    refine ⟨A 0, mem_image_of_mem A ?_⟩
    rw [hrep]
    simp
  let ht : ℝ × E →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ E
  have hlevel : ∀ p ∈ B, ht p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rfl
  have hcone := hbase.radialExtension hB ht hlevel
  have hconeT : FinitePiecewiseAffineOn T H := hcone.congr (by
    intro p hp
    obtain ⟨y, hy, r, hr, rfl⟩ := (mem_convexJoin_zero_iff B p).mp hp
    obtain ⟨x, hx, rfl⟩ := hy
    rw [ht.radialExtension_smul _ (show ht (A x) = 1 from rfl)]
    change r • G x = G.alexanderFamily (r * 1) (r • x)
    rw [mul_one]
    by_cases hr0 : r = 0
    · simp [hr0]
    · rw [G.alexanderFamily_apply_of_ne_zero hr0, inv_smul_smul₀ hr0])
  have hconeT' := hconeT
  obtain ⟨KH, hKH, hKHs, _⟩ := hconeT'
  obtain ⟨KI, hKI, hKIs⟩ := J.exists_finite_triangulation_inter KH hJ hKH
  rw [hKHs] at hKIs
  have hinside : FinitePiecewiseAffineOn T (J.space ∩ H) := by
    rw [← hKIs]
    exact hconeT.restrict KI hKI (hKIs.subset.trans inter_subset_right)
  have hpiece (a : (ℝ × E) →ᵃ[ℝ] ℝ)
      (heq : ∀ p ∈ J.space, a p ≤ 0 → T p = p.2) :
      FinitePiecewiseAffineOn T (J.space ∩ {p | a p ≤ 0}) := by
    obtain ⟨KP, hKP, hKPs⟩ := J.exists_finite_triangulation_inter_halfspaces hJ {a}
    simp only [Finset.mem_singleton, forall_eq] at hKPs
    have hp := (KP.affineOnFaces_affine
      (ContinuousLinearMap.snd ℝ ℝ E).toContinuousAffineMap).finitePiecewiseAffineOn hKP
    rw [hKPs] at hp
    exact hp.congr (fun p hp => (heq p hp.1 hp.2).symm)
  have hzero : FinitePiecewiseAffineOn T (J.space ∩ {p | p.1 ≤ 0}) :=
    hpiece ht.toAffineMap (by
      intro p hp hz
      have ht0 : p.1 = 0 := (show p.1 ≤ 0 from hz).antisymm (htime p hp).1
      simp [T, ht0])
  have houtside (i : ι) :
      FinitePiecewiseAffineOn T (J.space ∩ {p | p.1 ≤ L i p.2}) := by
    let a : (ℝ × E) →ᵃ[ℝ] ℝ :=
      ht.toAffineMap - ((L i).comp (LinearMap.snd ℝ ℝ E)).toAffineMap
    have heq (p : ℝ × E) (hp : p ∈ J.space) (ha : a p ≤ 0) : T p = p.2 := by
      have hi : p.1 ≤ L i p.2 := sub_nonpos.mp ha
      by_cases ht0 : p.1 = 0
      · simp [T, ht0]
      · have htpos : 0 < p.1 := lt_of_le_of_ne (htime p hp).1 (Ne.symm ht0)
        have hscaled : 1 ≤ L i (p.1⁻¹ • p.2) := by
          rw [map_smul, smul_eq_mul]
          exact (one_le_inv_mul₀ htpos).mpr hi
        dsimp only [T]
        rw [G.alexanderFamily_apply_of_ne_zero ht0, hfix i _ hscaled,
          smul_inv_smul₀ ht0]
    simpa only [a, AffineMap.coe_sub, Pi.sub_apply, LinearMap.coe_toAffineMap,
      LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      sub_nonpos, ht] using hpiece a heq
  have hcover : ((J.space ∩ H) ∪ (J.space ∩ {p | p.1 ≤ 0})) ∪
      (⋃ i, J.space ∩ {p | p.1 ≤ L i p.2}) = J.space := by
    apply Subset.antisymm
    · rintro p ((hp | hp) | hp)
      · exact hp.1
      · exact hp.1
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
        exact hi.1
    · intro p hp
      by_cases ht0 : p.1 ≤ 0
      · exact Or.inl (Or.inr ⟨hp, ht0⟩)
      have htpos : 0 < p.1 := lt_of_not_ge ht0
      by_cases hbound : ∀ i, L i p.2 ≤ p.1
      · apply Or.inl ∘ Or.inl
        refine ⟨hp, (mem_convexJoin_zero_iff B p).mpr ?_⟩
        have hxC : p.1⁻¹ • p.2 ∈ C := by
          rw [hrep]
          intro i
          rw [map_smul, smul_eq_mul]
          exact (inv_mul_le_one₀ htpos).mpr (hbound i)
        refine ⟨A (p.1⁻¹ • p.2), mem_image_of_mem A hxC, p.1, htime p hp, ?_⟩
        exact Prod.ext (by simp [A]) (by simp [A, smul_inv_smul₀ htpos.ne'])
      · push Not at hbound
        obtain ⟨i, hi⟩ := hbound
        exact Or.inr (mem_iUnion.mpr ⟨i, hp, hi.le⟩)
  have htotal := finitePiecewiseAffineOn_union
    (finitePiecewiseAffineOn_union hinside hzero) (FinitePiecewiseAffineOn.iUnion houtside)
  rwa [hcover] at htotal




theorem IsFinitePL.closedExtension_alexander_joint_finitePL
    {C : Set E} {e : C ≃ₜ C} (he : e.IsFinitePL) (hC : IsClosed C)
    (hfix : ∀ x : C, (x : E) ∈ frontier C → e x = x)
    {ι : Type*} [Finite ι] (L : ι → E →ₗ[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (hrep : C = {x | ∀ i, L i x ≤ 1})
    (J : SimplicialComplex ℝ (ℝ × E)) (hJ : J.faces.Finite)
    (htime : ∀ p ∈ J.space, p.1 ∈ Icc (0 : ℝ) 1) :
    let G := e.closedExtension hC hfix
    FinitePiecewiseAffineOn (fun p : ℝ × E => G.alexanderFamily p.1 p.2) J.space ∧
    FinitePiecewiseAffineOn (fun p : ℝ × E => (G.alexanderFamily p.1).symm p.2)
      J.space := by
  classical
  let G := e.closedExtension hC hfix
  have hGC : FinitePiecewiseAffineOn (G : E → E) C := by
    obtain ⟨f, hf, hef⟩ := he
    exact hf.congr (fun x hx => (hef ⟨x, hx⟩).symm.trans
      (e.closedExtension_apply_mem hC hfix hx).symm)
  have hGiC : FinitePiecewiseAffineOn (G.symm : E → E) C := by
    obtain ⟨f, hf, hef⟩ := he.symm
    apply hf.congr
    intro x hx
    apply G.injective
    rw [G.apply_symm_apply, ← hef ⟨x, hx⟩]
    change e.closedExtension hC hfix (e.symm ⟨x, hx⟩ : E) = x
    rw [e.closedExtension_apply_mem hC hfix (e.symm ⟨x, hx⟩).property]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  have hGfix (i : ι) (x : E) (hx : 1 ≤ L i x) : G x = x := by
    by_cases hxC : x ∈ C
    · have hbound : ∀ j, L j x ≤ 1 := by simpa only [hrep, mem_ofPred_eq] using hxC
      have hxfront : x ∈ frontier C := by
        rw [hrep, frontier_finite_linear_unit_halfspaces L hL]
        exact ⟨hbound, i, (hbound i).antisymm hx⟩
      exact e.closedExtension_apply_frontier hC hfix hxfront
    · exact e.closedExtension_apply_notMem hC hfix hxC
  refine ⟨G.alexanderFamily_joint_finitePL hGC L hrep hGfix J hJ htime, ?_⟩
  have hi := G.symm.alexanderFamily_joint_finitePL hGiC L hrep
    (fun i x hx => G.injective (by rw [G.apply_symm_apply, hGfix i x hx])) J hJ htime
  simpa only [alexanderFamily_symm] using hi




theorem IsFinitePL.exists_closedBall_joint_PL_isotopy
    {e : Metric.closedBall (0 : E) 1 ≃ₜ Metric.closedBall (0 : E) 1}
    (he : e.IsFinitePL)
    (hfix : ∀ x : Metric.closedBall (0 : E) 1, ‖(x : E)‖ = 1 → e x = x)
    {ι : Type*} [Finite ι] (L : ι → E →ₗ[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (hrep : Metric.closedBall (0 : E) 1 = {x | ∀ i, L i x ≤ 1}) :
    ∃ G : ℝ → E ≃ₜ E,
      G 0 = Homeomorph.refl E ∧ G 1 = e.closedBallExtension hfix ∧
      Continuous (fun p : ℝ × E => G p.1 p.2) ∧
      Continuous (fun p : ℝ × E => (G p.1).symm p.2) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, 1 ≤ ‖x‖ → G t x = x) ∧
      ∀ (J : SimplicialComplex ℝ (ℝ × E)), J.faces.Finite →
        (∀ p ∈ J.space, p.1 ∈ Icc (0 : ℝ) 1) →
        FinitePiecewiseAffineOn (fun p : ℝ × E => G p.1 p.2) J.space ∧
        FinitePiecewiseAffineOn (fun p : ℝ × E => (G p.1).symm p.2) J.space := by
  let g := e.closedBallExtension hfix
  have houtside : ∀ x, 1 ≤ ‖x‖ → g x = x := e.closedBallExtension_fixed_outside hfix
  have hbound := g.norm_sub_le_of_fixed_outside (by norm_num : (0 : ℝ) ≤ 1) houtside
  refine ⟨g.alexanderFamily, by simp, by simp [g],
    g.continuous_alexanderFamily hbound, g.continuous_alexanderFamily_symm hbound,
    fun t ht x hx => g.alexanderFamily_apply_of_fixed_outside houtside ht hx, ?_⟩
  intro J hJ htime
  exact he.closedExtension_alexander_joint_finitePL Metric.isClosed_closedBall
    (fun x hx => hfix x (by simpa only [Metric.mem_sphere, dist_zero_right] using
      Metric.frontier_closedBall_subset_sphere hx)) L hL hrep J hJ htime



theorem IsFinitePL.closedExtension_alexander_joint_finitePL_on_prism
    {C : Set E} {e : C ≃ₜ C} (he : e.IsFinitePL) (hC : IsClosed C)
    (hfix : ∀ x : C, (x : E) ∈ frontier C → e x = x)
    {ι : Type*} [Finite ι] (L : ι → E →ₗ[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (hrep : C = {x | ∀ i, L i x ≤ 1}) :
    let G := e.closedExtension hC hfix
    FinitePiecewiseAffineOn (fun p : ℝ × E => G.alexanderFamily p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ C) ∧
    FinitePiecewiseAffineOn (fun p : ℝ × E => (G.alexanderFamily p.1).symm p.2)
      (Icc (0 : ℝ) 1 ×ˢ C) := by
  classical
  let A : Finset (ℝ →ᵃ[ℝ] ℝ) :=
    {-AffineMap.id ℝ ℝ, AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 1}
  have hA : Icc (0 : ℝ) 1 = {x | ∀ a ∈ A, a x ≤ 0} := by
    ext x
    simp [A]
  obtain ⟨KI, hKI, hKIs⟩ := isCompact_Icc.exists_finite_triangulation_of_halfspaces A hA
  have he' := he
  obtain ⟨f, ⟨K, hK, hKs, _⟩, _⟩ := he'
  obtain ⟨J, hJ, hJs, _⟩ := KI.exists_finite_triangulation_prod K hKI hK
  rw [hKIs, hKs] at hJs
  have h := he.closedExtension_alexander_joint_finitePL hC hfix L hL hrep J hJ
    (fun p hp => (hJs ▸ hp).1)
  rwa [hJs] at h


theorem IsFinitePL.exists_square_joint_PL_isotopy
    {e : Metric.closedBall (0 : Fin 2 → ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin 2 → ℝ) 1}
    (he : e.IsFinitePL)
    (hfix : ∀ x : Metric.closedBall (0 : Fin 2 → ℝ) 1, ‖(x : Fin 2 → ℝ)‖ = 1 → e x = x) :
    ∃ G : ℝ → (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ),
      G 0 = Homeomorph.refl (Fin 2 → ℝ) ∧ G 1 = e.closedBallExtension hfix ∧
      Continuous (fun p : ℝ × (Fin 2 → ℝ) => G p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 2 → ℝ) => (G p.1).symm p.2) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, 1 ≤ ‖x‖ → G t x = x) ∧
      FinitePiecewiseAffineOn (fun p : ℝ × (Fin 2 → ℝ) => G p.1 p.2)
        (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Fin 2 → ℝ) 1) ∧
      FinitePiecewiseAffineOn (fun p : ℝ × (Fin 2 → ℝ) => (G p.1).symm p.2)
        (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Fin 2 → ℝ) 1) := by
  let L : Bool × Fin 2 → (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
    fun i => if i.1 then LinearMap.proj i.2 else -LinearMap.proj i.2
  have hL : ∀ i, L i ≠ 0 := by
    rintro ⟨b, i⟩ hz
    have h := congrArg (fun f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ => f (fun _ => 1)) hz
    cases b <;> norm_num [L] at h
  have hrep : Metric.closedBall (0 : Fin 2 → ℝ) 1 = {x | ∀ i, L i x ≤ 1} := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), Real.norm_eq_abs,
      abs_le, mem_ofPred_eq]
    constructor
    · intro hx ⟨b, i⟩
      cases b
      · simpa [L] using (neg_le_neg (hx i).1)
      · simpa [L] using (hx i).2
    · intro hx i
      have hn := hx (false, i)
      have hp := hx (true, i)
      simp only [L, Bool.false_eq_true, ↓reduceIte, LinearMap.neg_apply,
        LinearMap.proj_apply] at hn
      simp only [L, ↓reduceIte, LinearMap.proj_apply] at hp
      exact ⟨by linarith, hp⟩
  let g := e.closedBallExtension hfix
  have houtside : ∀ x, 1 ≤ ‖x‖ → g x = x := e.closedBallExtension_fixed_outside hfix
  have hbound := g.norm_sub_le_of_fixed_outside (by norm_num : (0 : ℝ) ≤ 1) houtside
  refine ⟨g.alexanderFamily, by simp, by simp [g],
    g.continuous_alexanderFamily hbound, g.continuous_alexanderFamily_symm hbound,
    fun t ht x hx => g.alexanderFamily_apply_of_fixed_outside houtside ht hx, ?_⟩
  exact he.closedExtension_alexander_joint_finitePL_on_prism Metric.isClosed_closedBall
    (fun x hx => hfix x (by simpa only [Metric.mem_sphere, dist_zero_right] using
      Metric.frontier_closedBall_subset_sphere hx)) L hL hrep

end Homeomorph
