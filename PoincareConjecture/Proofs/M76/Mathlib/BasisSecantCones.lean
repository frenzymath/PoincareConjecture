import PoincareConjecture.Proofs.M76.Mathlib.BasisConeCoordinates










set_option autoImplicit false

open Set

namespace Module.Basis

variable {ι E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



def secantCone (b : Basis ι ℝ E) (s t : Set ι) : Set E :=
  {x | (∀ i ∉ t, 0 ≤ b.repr x i) ∧ ∀ i ∉ s, b.repr x i ≤ 0}



theorem isClosed_secantCone [Finite ι] (b : Basis ι ℝ E) (s t : Set ι) :
    IsClosed (b.secantCone s t) := by
  classical
  let := Fintype.ofFinite ι
  have hc : ∀ i, Continuous (fun x : E => b.repr x i) :=
    fun i => (continuous_apply i).comp b.equivFunL.continuous
  change IsClosed {x : E | (∀ i ∉ t, 0 ≤ b.repr x i) ∧ ∀ i ∉ s, b.repr x i ≤ 0}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter (fun i => isClosed_iInter (fun _ : i ∉ t =>
    isClosed_le (continuous_const (y := (0 : ℝ))) (hc i)))).inter
    (isClosed_iInter (fun i => isClosed_iInter (fun _ : i ∉ s =>
      isClosed_le (hc i) (continuous_const (y := (0 : ℝ))))))



theorem smul_mem_secantCone (b : Basis ι ℝ E) {s t : Set ι} {x : E}
    (hx : x ∈ b.secantCone s t) {r : ℝ} (hr : 0 ≤ r) : r • x ∈ b.secantCone s t := by
  constructor
  · intro i hi
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using mul_nonneg hr (hx.1 i hi)
  · intro i hi
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
      mul_nonpos_of_nonneg_of_nonpos hr (hx.2 i hi)



theorem mem_secantCone_iff [Finite ι] (b : Basis ι ℝ E) (s t : Set ι) (z : E) :
    z ∈ b.secantCone s t ↔ ∃ x ∈ b.nonnegativeCone s,
      ∃ y ∈ b.nonnegativeCone t, z = x - y := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · intro hz
    let x := b.equivFunL.symm (fun i => max (b.repr z i) 0)
    let y := b.equivFunL.symm (fun i => max (-b.repr z i) 0)
    have hx : ∀ i, b.repr x i = max (b.repr z i) 0 :=
      fun i => congrFun (b.equivFunL.apply_symm_apply _) i
    have hy : ∀ i, b.repr y i = max (-b.repr z i) 0 :=
      fun i => congrFun (b.equivFunL.apply_symm_apply _) i
    refine ⟨x, ⟨fun i => ?_, fun i hi => ?_⟩,
      y, ⟨fun i => ?_, fun i hi => ?_⟩, ?_⟩
    · rw [hx]
      exact le_max_right _ _
    · rw [hx, max_eq_right (hz.2 i hi)]
    · rw [hy]
      exact le_max_right _ _
    · rw [hy, max_eq_right (neg_nonpos.mpr (hz.1 i hi))]
    · apply b.repr.injective
      ext i
      simp only [map_sub, Finsupp.sub_apply, hx, hy, max_zero_sub_eq_self]
  · rintro ⟨x, hx, y, hy, rfl⟩
    constructor
    · intro i hi
      simpa only [map_sub, Finsupp.sub_apply, hy.2 i hi, sub_zero] using hx.1 i
    · intro i hi
      simpa only [map_sub, Finsupp.sub_apply, hx.2 i hi, zero_sub] using neg_nonpos.mpr (hy.1 i)




theorem eq_zero_of_mem_secantCone_of_injOn [Finite ι] (b : Basis ι ℝ E) {s t : Set ι}
    (Q : E →L[ℝ] F)
    (hQ : InjOn Q (convexHull ℝ (insert 0 (b '' s)) ∪ convexHull ℝ (insert 0 (b '' t))))
    {z : E} (hz : z ∈ b.secantCone s t) (hQz : Q z = 0) : z = 0 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (b.mem_secantCone_iff s t z).mp hz
  obtain ⟨r, hr, u, hu, hru⟩ := b.exists_pos_smul_mem_simplex_of_mem_nonnegativeCone hx
  obtain ⟨q, hq, v, hv, hqv⟩ := b.exists_pos_smul_mem_simplex_of_mem_nonnegativeCone hy
  have hsum : 0 < r + q := add_pos hr hq
  let u' : E := (r / (r + q)) • u
  let v' : E := (q / (r + q)) • v
  have hu' : u' ∈ convexHull ℝ (insert 0 (b '' s)) :=
    (convex_convexHull ℝ _).smul_mem_of_zero_mem
      (subset_convexHull ℝ _ (mem_insert _ _)) hu
      ⟨div_nonneg hr.le hsum.le, (div_le_one hsum).mpr (by linarith)⟩
  have hv' : v' ∈ convexHull ℝ (insert 0 (b '' t)) :=
    (convex_convexHull ℝ _).smul_mem_of_zero_mem
      (subset_convexHull ℝ _ (mem_insert _ _)) hv
      ⟨div_nonneg hq.le hsum.le, (div_le_one hsum).mpr (by linarith)⟩
  have hru' : (r + q) • u' = x := by
    dsimp only [u']
    rw [smul_smul, mul_div_cancel₀ _ hsum.ne', hru]
  have hqv' : (r + q) • v' = y := by
    dsimp only [v']
    rw [smul_smul, mul_div_cancel₀ _ hsum.ne', hqv]
  have he : (r + q) • Q u' = (r + q) • Q v' := by
    rw [← map_smul, ← map_smul, hru', hqv']
    exact sub_eq_zero.mp (by simpa only [map_sub] using hQz)
  have he' : Q u' = Q v' := by
    have h := congrArg (fun w : F => (r + q)⁻¹ • w) he
    simpa only [inv_smul_smul₀ hsum.ne'] using h
  have huv := hQ (Or.inl hu') (Or.inr hv') he'
  have hxy : x = y := hru'.symm.trans ((congrArg (fun w : E => (r + q) • w) huv).trans hqv')
  exact sub_eq_zero.mpr hxy

end Module.Basis
