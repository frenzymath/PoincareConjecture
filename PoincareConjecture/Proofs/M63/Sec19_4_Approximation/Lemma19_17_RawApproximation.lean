import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.UniformSampledSmoothLoopFamily
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.UniformSampledChordLength
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.UniformFillingAreaComparison
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.CloseLoopFamilyHomotopy
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.FlattenedPolygonLength

set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareConjecture

theorem m63RawApproximation_nonempty
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (hnull : M61NullFamily Gamma) {zeta : ℝ} (hzeta : 0 < zeta) :
    Nonempty (M63RawApproximation F Gamma zeta) := by
  classical
  obtain ⟨_hbounded, _hattained, hL, hlength⟩ :=
    m63FamilyLengthSup_properties (F.metric a) Gamma
  obtain ⟨N0, _hN0pos, hchord⟩ :=
    M63.exists_uniform_sampled_chord_length (F.metric a) hcompact Gamma hzeta
  obtain ⟨deltaH, hdeltaH, hhom⟩ :=
    M63.exists_uniform_close_loop_family_homotopy (Z := LoopTwoSphere)
      (F.metric a) hcompact
  obtain ⟨deltaA, hdeltaA, harea⟩ :=
    m63_exists_uniform_filling_area_comparison (F.metric a) hcompact
      (Lambda := 2 * m63FamilyLengthSup (F.metric a) Gamma)
      (mul_nonneg (by norm_num) hL) hzeta
  obtain ⟨N, hN, hN0, polygon, hsample, family, hangular, hsmooth,
      hfirst, hsecond, hclose⟩ :=
    M63.exists_uniform_sampled_smooth_loop_family F hcompact Gamma N0
      (lt_min hdeltaH hdeltaA)
  have hcloseH (z : LoopTwoSphere) (x : LoopCircle) :
      (F.metric a).edist (family z x) (Gamma z x) < ENNReal.ofReal deltaH :=
    (hclose z x).trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hcloseA (z : LoopTwoSphere) (x : LoopCircle) :
      (F.metric a).edist (family z x) (Gamma z x) < ENNReal.ofReal deltaA :=
    (hclose z x).trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  have hlengthEq (z : LoopTwoSphere) : freeLoopLength (F.metric a) (family z) =
      ∑ j : Fin N, ((F.metric a).edist
        (periodicFreeLoop (Gamma z) (m63CellLeft N j))
        (periodicFreeLoop (Gamma z) (m63CellLeft N (finRotate N j)))).toReal := by
    have hrep : periodicFreeLoop (family z) = m63FlattenedPolygon (polygon z) :=
      funext (hangular z)
    have hflat : freeLoopLength (F.metric a) (family z) =
        m62Length F (fun x _ => m63FlattenedPolygon (polygon z) x) a := by
      unfold freeLoopLength
      rw [hrep]
      rfl
    rw [hflat, m63FlattenedPolygon_length F a (polygon z) hN]
    apply Finset.sum_congr rfl
    intro j _hj
    have hd := ((polygon z).side j).edist_eq_length (m63CellLength_pos hN).le
    have hchordSide := (congrArg₂ (F.metric a).edist
      (hsample z j) (hsample z (finRotate N j))).symm.trans hd
    rw [hchordSide, ENNReal.toReal_ofReal
      (mul_nonneg (m63CellLength_pos hN).le ((polygon z).side j).speed_nonnegative)]
  have hloss (z : LoopTwoSphere) :
      0 ≤ freeLoopLength (F.metric a) (Gamma z) - freeLoopLength (F.metric a) (family z) ∧
      freeLoopLength (F.metric a) (Gamma z) - freeLoopLength (F.metric a) (family z) < zeta := by
    rw [hlengthEq z]
    exact hchord N hN0 z
  obtain ⟨hhomotopic, htransfer⟩ := hhom Gamma family hcloseH
  have hfamilyNull : M61NullFamily family := fun z => htransfer z (hnull z)
  refine ⟨{
    count := N
    count_positive := hN
    polygon := polygon
    sample_eq := hsample
    family := family
    null_family := hfamilyNull
    homotopic := hhomotopic
    angular_eq := hangular
    angular_smooth := hsmooth
    first_jet_continuous := hfirst
    second_jet_continuous := hsecond
    length_loss := hloss
    area_error := ?_ }⟩
  intro z
  apply harea (Gamma z) (family z) (hnull z) (hfamilyNull z) (hcloseA z)
  linarith only [hlength z, (hloss z).1]

end PoincareConjecture
