import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal Manifold

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "T" => m64AnnulusHalfTurn

theorem M64ObservedWeakAnnulus.exists_halfTurn
    {e : M → E} {c0 c1 : ℝ → M}
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1)) :
    ∃ B : M64ObservedWeakAnnulus (n := n) e
      (c0 ∘ m64BoundaryHalfTurn) (c1 ∘ m64BoundaryHalfTurn),
      B.map = A.map ∘ T ∧
      (∀ i, ∀ᵐ p ∂mu, B.column i p = A.column i (T p)) := by
  let map := A.map ∘ T
  have hmap : MemLp (e ∘ map) 2 mu := by
    simpa only [map, Function.comp_def] using
      m64AnnulusHalfTurn_memLp A.observed_memLp
  have hcol (i : Fin 2) : MemLp (fun p => A.column i (T p)) 2 mu :=
    m64AnnulusHalfTurn_memLp (Lp.memLp (A.column i))
  let col := fun i => (hcol i).toLp (fun p => A.column i (T p))
  have hcol_ae (i : Fin 2) : (col i : LoopPlane → E) =ᵐ[mu]
      fun p => A.column i (T p) := (hcol i).coeFn_toLp
  have hmap_ae : (e ∘ map) =ᵐ[mu] fun p => e (A.map (T p)) := by
    filter_upwards [] with p
    rfl
  have htangent (i : Fin 2) : ∀ᵐ p ∂mu,
      col i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (map p)) := by
    have ha := m64AnnulusHalfTurn_measurePreserving.quasiMeasurePreserving.ae (A.tangent i)
    filter_upwards [ha, hcol_ae i] with p hp hcolp
    obtain ⟨v, hv⟩ := hp
    refine ⟨v, ?_⟩
    change (mfderiv (𝓡 n) (𝓡 m) e (A.map (T p))) v = col i p
    exact hv.trans hcolp.symm
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne
  have hu : Integrable (e ∘ A.map) mu := A.observed_memLp.integrable (by norm_num)
  have hV (i : Fin 2) : Integrable (A.column i) mu := (Lp.memLp _).integrable (by norm_num)
  have hgreenV : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p • A.column 1 p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) • e (A.map p)) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) • e (c1 x) - phi (annulusPoint x 0) • e (c0 x) := by
    intro phi hp
    simpa only [smul_eq_mul, mul_comm] using A.boundary phi hp
  have hgreenS : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p • A.column 0 p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) • e (A.map p)) = 0 := by
    intro phi hp hs
    simpa only [smul_eq_mul, mul_comm] using A.seam phi hp hs
  have hboundary : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p • col 1 p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) • e (map p)) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) • e ((c1 ∘ m64BoundaryHalfTurn) x) -
          phi (annulusPoint x 0) • e ((c0 ∘ m64BoundaryHalfTurn) x) := by
    intro phi hp
    have h := m64HalfTurn_vertical_green hu (hV 1) hc0 hc1 hgreenV hp
    have hcolint : (∫ p in S, phi p • col 1 p) =
        ∫ p in S, phi p • A.column 1 (T p) := by
      apply integral_congr_ae
      filter_upwards [hcol_ae 1] with p hp
      rw [hp]
    have hmapint : (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) •
        e (map p)) = ∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) •
          e (A.map (T p)) := by
      apply integral_congr_ae
      filter_upwards [] with p
      rfl
    rw [hcolint]
    simpa only [map, Function.comp_def, m64AnnulusHalfTurn_boundary_point] using h
  have hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p • col 0 p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) • e (map p)) = 0 := by
    intro phi hp hs
    have h := m64HalfTurn_seam_green hu (hV 0) hgreenS hp hs
    have hcolint : (∫ p in S, phi p • col 0 p) =
        ∫ p in S, phi p • A.column 0 (T p) := by
      apply integral_congr_ae
      filter_upwards [hcol_ae 0] with p hp
      rw [hp]
    rw [hcolint]
    simpa only [map, Function.comp_def] using h
  let B : M64ObservedWeakAnnulus (n := n) e
      (c0 ∘ m64BoundaryHalfTurn) (c1 ∘ m64BoundaryHalfTurn) := {
    map := map
    observed_memLp := hmap
    column := col
    tangent := htangent
    weak_partial := fun i b => by
      intro phi hp hcompact hsupp
      have hzero (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
          phi (annulusPoint curvePeriod s) = 0 ∧ phi (annulusPoint 0 s) = 0 := by
        have htop : annulusPoint curvePeriod s ∉ S := by
          intro hh
          exact lt_irrefl _ ((m64AnnulusInterior_coordinates _).mp hh).2.1
        have hbot : annulusPoint 0 s ∉ S := by
          intro hh
          exact lt_irrefl _ ((m64AnnulusInterior_coordinates _).mp hh).1
        constructor
        · apply image_eq_zero_of_notMem_tsupport
          intro hts
          exact htop (hsupp hts)
        · apply image_eq_zero_of_notMem_tsupport
          intro hts
          exact hbot (hsupp hts)
      have hsperiod : ∀ s ∈ Icc (0 : ℝ) 1,
          phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s) := by
        intro s hs
        obtain ⟨ht, hb⟩ := hzero s hs
        rw [ht, hb]
      have hphi : MemLp phi 2 mu :=
        (hp.continuous.memLp_of_hasCompactSupport hcompact)
      have hD : MemLp (fun p => fderiv ℝ phi p
          (EuclideanSpace.single (0 : Fin 2) 1)) 2 mu :=
        (((hp.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
          (hcompact.fderiv_apply ℝ _))
      have hzero_bottom (x : ℝ) : phi (annulusPoint x 0) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hts
        have hh := (m64AnnulusInterior_coordinates _).mp (hsupp hts)
        exact (lt_irrefl (0 : ℝ)) ((by simpa [annulusPoint] using hh.2.2.1) : (0 : ℝ) < 0)
      have hzero_top (x : ℝ) : phi (annulusPoint x 1) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hts
        exact lt_irrefl _ ((m64AnnulusInterior_coordinates _).mp (hsupp hts)).2.2.2
      have hproj (L : E →L[ℝ] ℝ) {f : LoopPlane → E}
          (hf : MemLp f 2 mu) {psi : LoopPlane → ℝ} (hpsi : MemLp psi 2 mu) :
          L (∫ p in S, psi p • f p) =
            ∫ p in S, psi p * L (f p) := by
        simpa only [map_smul, smul_eq_mul] using
          (L.integral_comp_comm (m64L2_test_integrable hf hpsi)).symm
      have hi : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
        fin_cases i <;> simp
      rcases hi with rfl | rfl
      · have h := hseam phi (hp.of_le (by simp)) hsperiod
        change (∫ p in S, phi p • col 0 p) +
            (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) •
              (e ∘ map) p) = 0 at h
        let L := EuclideanSpace.proj (𝕜 := ℝ) b
        have hs := congrArg L h
        rw [map_add, map_zero, hproj L (Lp.memLp (col 0)) hphi,
          hproj L hmap hD] at hs
        have hswap : (∫ p in S, phi p * L (col 0 p)) =
            ∫ p in S, L (col 0 p) * phi p := by
          apply integral_congr_ae
          filter_upwards [] with p
          ring
        rw [hswap] at hs
        simp only [L, EuclideanSpace.coe_proj, Function.comp_def, mul_comm] at hs ⊢
        apply eq_neg_iff_add_eq_zero.mpr
        convert hs using 1
        ring
      · have h := hboundary phi (hp.of_le (by simp))
        change (∫ p in S, phi p • col 1 p) +
            (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) •
              (e ∘ map) p) =
            ∫ x in Icc (0 : ℝ) curvePeriod,
                phi (annulusPoint x 1) • e ((c1 ∘ m64BoundaryHalfTurn) x) -
                  phi (annulusPoint x 0) • e ((c0 ∘ m64BoundaryHalfTurn) x) at h
        have hbdzero :
            (∫ x in Icc (0 : ℝ) curvePeriod,
              phi (annulusPoint x 1) • e ((c1 ∘ m64BoundaryHalfTurn) x) -
                phi (annulusPoint x 0) • e ((c0 ∘ m64BoundaryHalfTurn) x)) = 0 := by
          apply integral_eq_zero_of_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
          simp [hzero_top x, hzero_bottom x]
        rw [hbdzero] at h
        let L := EuclideanSpace.proj (𝕜 := ℝ) b
        have hD1 : MemLp (fun p => fderiv ℝ phi p
            (EuclideanSpace.single (1 : Fin 2) 1)) 2 mu :=
          (((hp.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
            (hcompact.fderiv_apply ℝ _))
        have hs := congrArg L h
        rw [map_add, map_zero, hproj L (Lp.memLp (col 1)) hphi,
          hproj L hmap hD1] at hs
        have hswap : (∫ p in S, phi p * L (col 1 p)) =
            ∫ p in S, L (col 1 p) * phi p := by
          apply integral_congr_ae
          filter_upwards [] with p
          ring
        rw [hswap] at hs
        simp only [L, EuclideanSpace.coe_proj, Function.comp_def, mul_comm] at hs ⊢
        apply eq_neg_iff_add_eq_zero.mpr
        convert hs using 1
        ring
    boundary := hboundary
    seam := hseam }
  refine ⟨B, rfl, ?_⟩
  intro i
  exact hcol_ae i

end PoincareConjecture
