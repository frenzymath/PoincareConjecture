import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLGluing
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import Mathlib.Topology.Path









set_option autoImplicit false

open Set Geometry

namespace Path

variable {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X F} {a b c : X}

private theorem interval_carrier {u v : ℝ} (huv : u < v) :
    ∃ K : SimplicialComplex ℝ ℝ, K.faces.Finite ∧ K.space = Icc u v := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc huv
  exact ⟨K, hK, hKs⟩

omit [FiniteDimensional ℝ F] in


theorem polyhedralPL_extend_symm (p : Path a b)
    (hp : PolyhedralPLInCharts e p.extend (Icc (0 : ℝ) 1)) :
    PolyhedralPLInCharts e p.symm.extend (Icc (0 : ℝ) 1) := by
  obtain ⟨K, hK, hKs⟩ := interval_carrier (show (0 : ℝ) < 1 from zero_lt_one)
  let A : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ ℝ 1 - ContinuousAffineMap.id ℝ ℝ
  have hA : MapsTo A K.space (Icc (0 : ℝ) 1) := by
    intro t ht
    have htI := hKs.subset ht
    change 1 - t ∈ Icc (0 : ℝ) 1
    exact ⟨by linarith [htI.2], by linarith [htI.1]⟩
  have hcomp := hp.comp_finitePiecewiseAffineOn K hK
    ((K.affineOnFaces_affine A).finitePiecewiseAffineOn hK) hA
  rw [← hKs]
  apply hcomp.congr
  intro t _
  change p.extend (1 - t) = p.symm.extend t
  exact (p.extend_symm_apply t).symm




theorem polyhedralPL_extend_trans
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (p : Path a b) (q : Path b c)
    (hp : PolyhedralPLInCharts e p.extend (Icc (0 : ℝ) 1))
    (hq : PolyhedralPLInCharts e q.extend (Icc (0 : ℝ) 1)) :
    PolyhedralPLInCharts e (p.trans q).extend (Icc (0 : ℝ) 1) := by
  obtain ⟨K, hK, hKs⟩ := interval_carrier (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨K0, hK0, hK0s⟩ := interval_carrier (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨K1, hK1, hK1s⟩ := interval_carrier (show (1 / 2 : ℝ) < 1 by norm_num)
  let A0 : ℝ →ᴬ[ℝ] ℝ := (2 : ℝ) • ContinuousAffineMap.id ℝ ℝ
  let A1 : ℝ →ᴬ[ℝ] ℝ := A0 - ContinuousAffineMap.const ℝ ℝ 1
  have hA0 : MapsTo A0 K0.space (Icc (0 : ℝ) 1) := by
    intro t ht
    have htI := hK0s.subset ht
    change 2 * t ∈ Icc (0 : ℝ) 1
    exact ⟨by linarith [htI.1], by linarith [htI.2]⟩
  have hA1 : MapsTo A1 K1.space (Icc (0 : ℝ) 1) := by
    intro t ht
    have htI := hK1s.subset ht
    change 2 * t - 1 ∈ Icc (0 : ℝ) 1
    exact ⟨by linarith [htI.1], by linarith [htI.2]⟩
  have hleft : PolyhedralPLInCharts e (p.trans q).extend K0.space := by
    apply (hp.comp_finitePiecewiseAffineOn K0 hK0
      ((K0.affineOnFaces_affine A0).finitePiecewiseAffineOn hK0) hA0).congr
    intro t ht
    change p.extend (2 * t) = (p.trans q).extend t
    exact (p.extend_trans_of_le_half q (hK0s.subset ht).2).symm
  have hright : PolyhedralPLInCharts e (p.trans q).extend K1.space := by
    apply (hq.comp_finitePiecewiseAffineOn K1 hK1
      ((K1.affineOnFaces_affine A1).finitePiecewiseAffineOn hK1) hA1).congr
    intro t ht
    change q.extend (2 * t - 1) = (p.trans q).extend t
    exact (p.extend_trans_of_half_le q (hK1s.subset ht).1).symm
  let J : Bool → SimplicialComplex ℝ ℝ := fun j => if j then K1 else K0
  have hJ (j : Bool) : (J j).faces.Finite := by cases j <;> assumption
  have hPL (j : Bool) : PolyhedralPLInCharts e (p.trans q).extend (J j).space := by
    cases j <;> assumption
  have hcoverK : K.space ⊆ ⋃ j, (J j).space := by
    intro t ht
    have htI := hKs.subset ht
    by_cases h : t ≤ 1 / 2
    · exact mem_iUnion.mpr ⟨false, hK0s.symm.subset ⟨htI.1, h⟩⟩
    · exact mem_iUnion.mpr ⟨true, hK1s.symm.subset ⟨(lt_of_not_ge h).le, htI.2⟩⟩
  rw [← hKs]
  exact polyhedralPLInCharts_of_finite_cover hcover hcompat K hK J hJ
    (p.trans q).continuous_extend.continuousOn hPL hcoverK

end Path
