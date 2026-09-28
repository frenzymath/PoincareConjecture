import PoincareConjecture.Proofs.M03.Existence.LocalOrthonormalFrameNative
import PoincareConjecture.Proofs.M03.Existence.TensorProbeL2Native
import Mathlib.Geometry.Manifold.PartitionOfUnity









set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

noncomputable section

universe u v

namespace PoincareConjecture.ParsevalFrameNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

variable {iota : Type v} [Fintype iota]

def partitionSquareSum (phi : iota → M → ℝ) (x : M) : ℝ := ∑ i, phi i x ^ 2

theorem partitionSquareSum_pos (phi : iota → M → ℝ)
    (hsum : ∀ x, ∑ i, phi i x = 1) (x : M) : 0 < partitionSquareSum phi x := by
  classical
  have hex : ∃ i, phi i x ≠ 0 := by
    by_contra h
    push_neg at h
    have hs := hsum x
    simp only [h, Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨i, hi⟩ := hex
  exact (sq_pos_of_ne_zero hi).trans_le
    (Finset.single_le_sum (fun j _ => sq_nonneg (phi j x)) (Finset.mem_univ i))

private theorem contMDiff_scalar_finset_sum {jota : Type*}
    (f : jota → M → ℝ) (s : Finset jota)
    (hf : ∀ j ∈ s, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => ∑ j ∈ s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using contMDiff_const (c := (0 : ℝ))
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (hf j (Finset.mem_insert_self j s)).add
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

theorem partitionSquareSum_contMDiff (phi : iota → M → ℝ)
    (hphi : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (phi i)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (partitionSquareSum phi) := by
  have hterm (i : iota) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => phi i x ^ 2) := by
    simpa only [pow_two, smul_eq_mul, Pi.mul_def] using (hphi i).smul (hphi i)
  exact contMDiff_scalar_finset_sum _ Finset.univ (fun i _ => hterm i)

def partitionNormalizer (phi : iota → M → ℝ) (x : M) : ℝ :=
  (Real.sqrt (partitionSquareSum phi x))⁻¹

theorem partitionNormalizer_contMDiff (phi : iota → M → ℝ)
    (hphi : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (phi i))
    (hsum : ∀ x, ∑ i, phi i x = 1) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (partitionNormalizer phi) := by
  apply contMDiffOn_univ.mp
  exact contMDiffOn_scalar_inverse
    (contMDiffOn_scalar_sqrt (partitionSquareSum_contMDiff phi hphi).contMDiffOn
      (fun x _ => ne_of_gt (partitionSquareSum_pos phi hsum x)))
    (fun x _ => ne_of_gt (Real.sqrt_pos.mpr (partitionSquareSum_pos phi hsum x)))

theorem partitionNormalizer_sum_sq (phi : iota → M → ℝ)
    (hsum : ∀ x, ∑ i, phi i x = 1) (x : M) :
    (∑ i, (partitionNormalizer phi x * phi i x) ^ 2) = 1 := by
  have hpos := partitionSquareSum_pos phi hsum x
  calc
    (∑ i, (partitionNormalizer phi x * phi i x) ^ 2) =
        (partitionNormalizer phi x) ^ 2 * partitionSquareSum phi x := by
      simp only [mul_pow, Finset.mul_sum, partitionSquareSum]
    _ = 1 := by
      rw [partitionNormalizer, inv_pow, Real.sq_sqrt hpos.le]
      exact inv_mul_cancel₀ hpos.ne'

def normalizedChartField (g : RiemannianMetric n M) (p : iota → M)
    (phi : iota → M → ℝ) (ij : iota × Fin n) (x : M) : TangentSpace (𝓡 n) x :=
  partitionNormalizer phi x • (phi ij.1 x • chartOrthonormalFrame g (p ij.1) ij.2 x)

theorem normalizedChartField_contMDiff (g : RiemannianMetric n M) (p : iota → M)
    (phi : iota → M → ℝ) (hphi : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (phi i))
    (hsum : ∀ x, ∑ i, phi i x = 1)
    (hsupport : ∀ i, tsupport (phi i) ⊆ (chartAt E (p i)).source) (ij : iota × Fin n) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (normalizedChartField g p phi ij)) := by
  have hcut := (hphi ij.1).contMDiffOn.smul_section_of_tsupport
    (chartAt E (p ij.1)).open_source (hsupport ij.1)
    (chartOrthonormalFrame_contMDiffOn g (p ij.1) ij.2)
  exact (partitionNormalizer_contMDiff phi hphi hsum).smul_section hcut

theorem normalizedChartField_sum_repr (g : RiemannianMetric n M) (p : iota → M)
    (phi : iota → M → ℝ) (hsum : ∀ x, ∑ i, phi i x = 1)
    (hsupport : ∀ i, tsupport (phi i) ⊆ (chartAt E (p i)).source)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (∑ ij : iota × Fin n,
      g.inner x (normalizedChartField g p phi ij x) v • normalizedChartField g p phi ij x) = v := by
  classical
  have hlocal (i : iota) :
      (∑ j : Fin n, g.inner x (normalizedChartField g p phi (i, j) x) v •
        normalizedChartField g p phi (i, j) x) =
          (partitionNormalizer phi x * phi i x) ^ 2 • v := by
    by_cases hzero : phi i x = 0
    · simp [normalizedChartField, hzero]
    have hx : x ∈ (chartAt E (p i)).source :=
      hsupport i (subset_tsupport (phi i) hzero)
    calc
      (∑ j : Fin n, g.inner x (normalizedChartField g p phi (i, j) x) v •
          normalizedChartField g p phi (i, j) x) =
          (partitionNormalizer phi x * phi i x) ^ 2 •
            (∑ j : Fin n, g.inner x (chartOrthonormalFrame g (p i) j x) v •
              chartOrthonormalFrame g (p i) j x) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [normalizedChartField, map_smul, ContinuousLinearMap.smul_apply,
          smul_eq_mul, smul_smul]
        congr 1
        ring
      _ = _ := by rw [chartOrthonormalFrame_sum_repr g (p i) x hx v]
  calc
    (∑ ij : iota × Fin n,
        g.inner x (normalizedChartField g p phi ij x) v • normalizedChartField g p phi ij x) =
        ∑ i, ∑ j : Fin n, g.inner x (normalizedChartField g p phi (i, j) x) v •
          normalizedChartField g p phi (i, j) x := Fintype.sum_prod_type _
    _ = ∑ i, (partitionNormalizer phi x * phi i x) ^ 2 • v :=
      Finset.sum_congr rfl (fun i _ => hlocal i)
    _ = (∑ i, (partitionNormalizer phi x * phi i x) ^ 2) • v := (Finset.sum_smul).symm
    _ = v := by rw [partitionNormalizer_sum_sq phi hsum x, one_smul]


theorem exists_finite_smooth_parseval_fields [T2Space M] [CompactSpace M]
    (g : RiemannianMetric n M) :
    ∃ k : ℕ, ∃ F : Fin k → TensorProbeNative.SmoothField (n := n) (M := M),
      ∀ (x : M) (v : TangentSpace (𝓡 n) x),
        (∑ i, g.inner x (F i x) v • F i x) = v := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun p : M => (chartAt E p).source) (fun p => (chartAt E p).open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_chart_source E x⟩)
  let p : s → M := Subtype.val
  have hcover : (univ : Set M) ⊆ ⋃ i : s, (chartAt E (p i)).source := by
    intro x hx
    have h := hs hx
    simp only [mem_iUnion] at h
    obtain ⟨y, hys, hxy⟩ := h
    exact mem_iUnion.mpr ⟨⟨y, hys⟩, hxy⟩
  obtain ⟨phi, hphi⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓡 n)
    isClosed_univ (fun i : s => (chartAt E (p i)).source)
    (fun i => (chartAt E (p i)).open_source) hcover
  have hsmooth (i : s) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (phi i) := (phi i).contMDiff
  have hsum (x : M) : ∑ i : s, phi i x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using phi.sum_eq_one (mem_univ x)
  let F : s × Fin n → TensorProbeNative.SmoothField (n := n) (M := M) := fun ij =>
    ⟨normalizedChartField g p (fun i x => phi i x) ij,
      normalizedChartField_contMDiff g p (fun i x => phi i x) hsmooth hsum hphi ij⟩
  let e := Fintype.equivFin (s × Fin n)
  refine ⟨Fintype.card (s × Fin n), fun j => F (e.symm j), ?_⟩
  intro x v
  calc
    (∑ j, g.inner x (F (e.symm j) x) v • F (e.symm j) x) =
        ∑ ij : s × Fin n, g.inner x (F ij x) v • F ij x :=
      e.symm.sum_comp (fun ij : s × Fin n => g.inner x (F ij x) v • F ij x)
    _ = v := normalizedChartField_sum_repr g p (fun i x => phi i x) hsum hphi x v

end PoincareConjecture.ParsevalFrameNative

end
