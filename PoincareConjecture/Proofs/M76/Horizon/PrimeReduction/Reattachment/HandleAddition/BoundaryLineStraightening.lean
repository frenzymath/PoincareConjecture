import PoincareConjecture.Proofs.M76.Wall.Mathlib.DistinctRayStraightening
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76


theorem exists_two_ray_straightening_preserving_plane
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] ℝ) {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hne : ∀ t : ℝ,0 < t → u ≠ t • v) (hAu : A u = 0) (hAv : A v = 0) :
    ∃ (ell : E →L[ℝ] ℝ) (w : E),ell u < 0 ∧ ell v = 1 ∧ ell w = 1 ∧
      A w = 0 ∧ ∃ H : E ≃ₜ E,
        H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧ H 0 = 0 ∧
        (∀ x,A (H x) = A x) ∧
        (∀ t : ℝ,0 ≤ t → H (t • u) = (t * ell u) • w) ∧
        ∀ t : ℝ,0 ≤ t → H (t • v) = t • w := by
  obtain ⟨ell,hellu,hellv⟩ := ContinuousLinearMap.exists_height_of_distinct_rays hu hv hne
  let a : E := (ell u)⁻¹ • u - v
  have ha : ell a = 0 := by
    simp [a,hellv,inv_mul_cancel₀ hellu.ne]
  have hAa : A a = 0 := by simp [a,hAu,hAv]
  obtain ⟨H,hHPL,hH,_,_⟩ := ell.exists_two_halfspace_shear a 0 ha (map_zero _)
  refine ⟨ell,v,hellu,hellv,hellv,hAv,H,hHPL,?_,?_,?_,?_⟩
  · simp [hH]
  · intro x
    simp [hH,hAa]
  · intro t ht
    have hs : ell (t • u) ≤ 0 := by
      simpa only [map_smul,smul_eq_mul] using mul_nonpos_of_nonneg_of_nonpos ht hellu.le
    rw [hH,min_eq_left hs,smul_zero,sub_zero]
    simp only [map_smul,smul_eq_mul]
    change t • u - (t * ell u) • ((ell u)⁻¹ • u - v) = (t * ell u) • v
    rw [smul_sub,smul_smul,mul_assoc,mul_inv_cancel₀ hellu.ne,mul_one]
    abel
  · intro t ht
    have hs : 0 ≤ ell (t • v) := by simpa [hellv] using ht
    rw [hH,min_eq_right hs,zero_smul,sub_zero,smul_zero,sub_zero]


theorem exists_plane_line_functionals
    (A : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (hA : A ≠ 0)
    {w : Fin 3 → ℝ} (hw : w ≠ 0) (hAw : A w = 0) :
    ∃ (psi : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (u v : Fin 3 → ℝ),
      A u = 0 ∧ psi u = 1 ∧ A v = 1 ∧ psi v = 0 ∧
      ∀ x,A x = 0 ∧ psi x = 0 ↔ ∃ t : ℝ,x = t • w := by
  let W : Submodule ℝ (Fin 3 → ℝ) := ℝ ∙ w
  have hW : Module.finrank ℝ W = 1 := finrank_span_singleton hw
  have hker : Module.finrank ℝ A.ker = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hA
    have hd : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
    omega
  have hWA : W ≤ A.ker := Submodule.span_le.mpr (singleton_subset_iff.mpr hAw)
  have hnot : ¬A.ker ≤ W := by
    intro h
    have hh := Submodule.finrank_mono h
    rw [hW,hker] at hh
    omega
  obtain ⟨u,huA,huW⟩ := Set.not_subset.mp hnot
  obtain ⟨phi,hphi,hphiW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem huW inferInstance
  have hphiw : phi w = 0 := by
    have hh : phi w ∈ W.map phi := ⟨w,Submodule.mem_span_singleton_self w,rfl⟩
    rw [hphiW] at hh
    exact hh
  let psi : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := (phi u)⁻¹ • phi
  have hpu : psi u = 1 := by simp [psi,inv_mul_cancel₀ hphi]
  have hpw : psi w = 0 := by simp [psi,hphiw]
  have hWApsi : W ≤ A.ker ⊓ psi.ker := Submodule.span_le.mpr
    (singleton_subset_iff.mpr ⟨hAw,hpw⟩)
  have hlt : A.ker ⊓ psi.ker < A.ker := lt_of_le_of_ne inf_le_left (by
    intro heq
    have hh : u ∈ A.ker ⊓ psi.ker := heq.symm ▸ huA
    have hz : psi u = 0 := hh.2
    rw [hpu] at hz
    exact one_ne_zero hz)
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  have heq : W = A.ker ⊓ psi.ker := Submodule.eq_of_le_of_finrank_le hWApsi (by
    rw [hker] at hdim
    rw [hW]
    omega)
  have hex : ∃ z,A z ≠ 0 := by
    by_contra! h
    apply hA
    apply LinearMap.ext
    intro z
    exact h z
  obtain ⟨z,hz⟩ := hex
  let normal : Fin 3 → ℝ := (A z)⁻¹ • z
  have hn : A normal = 1 := by simp [normal,inv_mul_cancel₀ hz]
  let v := normal - psi normal • u
  have hAu : A u = 0 := huA
  refine ⟨psi,u,v,hAu,hpu,?_,?_,?_⟩
  · simp [v,hn,hAu]
  · simp [v,hpu]
  · intro x
    change x ∈ A.ker ⊓ psi.ker ↔ _
    rw [←heq,Submodule.mem_span_singleton]
    exact exists_congr (fun t => eq_comm)


theorem exists_compatible_plane_rim_chart_of_rays
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (B : OpenPartialHomeomorph X (Fin 3 → ℝ))
    (hcompat : ∀ i,(e i).symm.trans B ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (A : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (hA : A ≠ 0)
    {F L U : Set X} {x : X} (hxB : x ∈ B.source) (hBx : B x = 0)
    (hfront : ∀ y ∈ B.source,y ∈ F ↔ A (B y) = 0)
    (hU : IsOpen U) (hxU : x ∈ U)
    {u v : Fin 3 → ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hne : ∀ t : ℝ,0 < t → u ≠ t • v) (hAu : A u = 0) (hAv : A v = 0)
    (hrays : ∀ y ∈ U,y ∈ L ↔
      (∃ t : ℝ,0 ≤ t ∧ B y = t • u) ∨ ∃ t : ℝ,0 ≤ t ∧ B y = t • v) :
    ∃ (T : OpenPartialHomeomorph X (Fin 3 → ℝ))
      (ell psi : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ) (a b : Fin 3 → ℝ),
      x ∈ T.source ∧ T.source ⊆ U ∧ T x = 0 ∧
      (∀ i,(e i).symm.trans T ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
      ell.contLinear a = 0 ∧ psi.contLinear a = 1 ∧
      ell.contLinear b = 1 ∧ psi.contLinear b = 0 ∧
      (∀ y ∈ T.source,y ∈ F ↔ ell (T y) = 0) ∧
      ∀ y ∈ T.source,y ∈ L ↔ ell (T y) = 0 ∧ psi (T y) = 0 := by
  obtain ⟨h,w,hhu,_,hhw,hAw,H,hHPL,hH0,hHA,hHu,hHv⟩ :=
    exists_two_ray_straightening_preserving_plane A hu hv hne hAu hAv
  have hw : w ≠ 0 := by intro he; rw [he,map_zero] at hhw; exact zero_ne_one hhw
  obtain ⟨psi,a,b,hAa,hpa,hAb,hpb,hline⟩ := exists_plane_line_functionals A hA hw hAw
  let T := (B.restrOpen U hU).trans H.toOpenPartialHomeomorph
  have hTs : T.source = B.source ∩ U := by
    change (B.source ∩ U) ∩ B ⁻¹' univ = B.source ∩ U
    rw [preimage_univ,inter_univ]
  refine ⟨T,A.toContinuousLinearMap.toContinuousAffineMap,
    psi.toContinuousLinearMap.toContinuousAffineMap,a,b,hTs.symm.subset ⟨hxB,hxU⟩,
    fun y hy => (hTs.subset hy).2,?_,?_,hAa,hpa,hAb,hpb,?_,?_⟩
  · change H (B x) = 0
    rw [hBx,hH0]
  · intro i
    have hi := (e i).piecewiseAffine_compatible_restrOpen_right B (hcompat i) hU
    simpa only [T,←OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid (Fin 3 → ℝ)).trans hi hHPL
  · intro y hy
    change y ∈ F ↔ A (H (B y)) = 0
    rw [hHA]
    exact hfront y (hTs.subset hy).1
  · intro y hy
    change y ∈ L ↔ A (H (B y)) = 0 ∧ psi (H (B y)) = 0
    rw [hline,hrays y (hTs.subset hy).2]
    constructor
    · rintro (⟨t,ht,hyt⟩ | ⟨t,ht,hyt⟩)
      · exact ⟨t * h u,by rw [hyt,hHu t ht]⟩
      · exact ⟨t,by rw [hyt,hHv t ht]⟩
    · rintro ⟨r,hr⟩
      by_cases hr0 : r ≤ 0
      · have ht : 0 ≤ r / h u := div_nonneg_of_nonpos hr0 hhu.le
        refine Or.inl ⟨r / h u,ht,H.injective ?_⟩
        rw [hHu _ ht,div_mul_cancel₀ _ hhu.ne]
        exact hr
      · have ht : 0 ≤ r := (lt_of_not_ge hr0).le
        exact Or.inr ⟨r,ht,H.injective (hr.trans (hHv r ht).symm)⟩


end PoincareConjecture.M76

