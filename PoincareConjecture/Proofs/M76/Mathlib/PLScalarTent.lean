import PoincareConjecture.Proofs.M76.Mathlib.PLFiberCompression











set_option autoImplicit false

open Set Geometry

namespace PLScalarTent




noncomputable def value (r R s : ℝ) : ℝ :=
  min 1 (max 0 ((R - |s|) / (R - r)))



theorem value_mem_unit (r R s : ℝ) : value r R s ∈ Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩



theorem value_eq_one {r R s : ℝ} (hrR : r < R) (hs : |s| ≤ r) :
    value r R s = 1 := by
  have h : 1 ≤ (R - |s|) / (R - r) :=
    (one_le_div (sub_pos.mpr hrR)).mpr (by linarith)
  exact min_eq_left (h.trans (le_max_right _ _))



theorem value_eq_zero {r R s : ℝ} (hrR : r < R) (hs : R ≤ |s|) :
    value r R s = 0 := by
  unfold value
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (sub_pos.mpr hrR).le)]
  norm_num



theorem continuous_value (r R : ℝ) : Continuous (value r R) := by
  unfold value
  fun_prop




theorem finitePiecewiseAffineOn_value (r R : ℝ)
    (K : SimplicialComplex ℝ ℝ) (hK : K.faces.Finite) :
    FinitePiecewiseAffineOn (value r R) K.space := by
  have hi := (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)).finitePiecewiseAffineOn hK
  have hn := (K.affineOnFaces_affine (-ContinuousAffineMap.id ℝ ℝ)).finitePiecewiseAffineOn hK
  have habs : FinitePiecewiseAffineOn (abs : ℝ → ℝ) K.space :=
    (hi.max hn).congr (fun _ _ => abs_eq_max_neg.symm)
  have hR := (K.affineOnFaces_affine
    (ContinuousAffineMap.const ℝ ℝ R)).finitePiecewiseAffineOn hK
  have hone := (K.affineOnFaces_affine
    (ContinuousAffineMap.const ℝ ℝ (1 : ℝ))).finitePiecewiseAffineOn hK
  have hdiv : FinitePiecewiseAffineOn (fun s => (R - |s|) / (R - r)) K.space := by
    apply ((hR.sub habs).postcomp ((R - r)⁻¹ • ContinuousAffineMap.id ℝ ℝ)).congr
    intro s _
    change (R - r)⁻¹ * (R - |s|) = (R - |s|) / (R - r)
    rw [div_eq_mul_inv, mul_comm]
  exact hone.min hdiv.positivePart



theorem locallyPiecewiseAffineOn_value (r R : ℝ) :
    LocallyPiecewiseAffineOn (value r R) univ := by
  intro x _
  obtain ⟨K, hK, hxK, _⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed
      isCompact_singleton isOpen_univ (singleton_subset_iff.mpr (mem_univ x))
  obtain ⟨J, hJ, hJK, hv⟩ := finitePiecewiseAffineOn_value r R K hK
  refine ⟨J, hJ, ?_, fun _ _ => mem_univ _, hv⟩
  rw [hJK]
  exact hxK (mem_singleton x)

end PLScalarTent
