import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ScaledJetDissipation
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ShortTimeFirstJet
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FiniteJetComparison
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ProductAmbientDerivativeBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.LocalCurveTheory
import PoincareConjecture.Proofs.M63.Adapters

set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

set_option maxHeartbeats 400000 in

theorem m63CircleProduct_curvatureJetSquared_bound_of_inverse_age [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    (G : M63AmbientGeometry F) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (circumference : ℝ) (h : 0 < circumference),
        let P := G.product circumference h
        ∀ c : ℝ → ℝ → P.charts.Point,
          M63C2ShrinkingCurveOn P.flow c (Icc a b) →
          ∀ s T : ℝ, a ≤ s → s < T → T ≤ b → T - s ≤ 1 →
            (∀ t ∈ Ioo s T, ∀ x, m63CurvatureJetSquared P.flow c 0 t x ≤ 2 / (t - s)) →
            ∀ t ∈ Ioo s T, ∀ i x,
              m63CurvatureJetSquared P.flow c i t x ≤ C i / (t - s) ^ (i + 1) := by
  classical
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  obtain ⟨Kseq, hKseq, hTensor⟩ :=
    m63CircleProduct_uniform_curvature_derivative_bounds F hcompact
  let Bound : ℕ → ℝ → Prop := fun i C =>
    ∀ (circumference : ℝ) (h : 0 < circumference),
      let P := G.product circumference h
      ∀ c : ℝ → ℝ → P.charts.Point,
        M63C2ShrinkingCurveOn P.flow c (Icc a b) →
        ∀ s T : ℝ, a ≤ s → s < T → T ≤ b → T - s ≤ 1 →
          (∀ t ∈ Ioo s T, ∀ x, m63CurvatureJetSquared P.flow c 0 t x ≤ 2 / (t - s)) →
          ∀ t ∈ Ioo s T, ∀ x,
            m63CurvatureJetSquared P.flow c i t x ≤ C / (t - s) ^ (i + 1)
  have hbound (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ Bound m C := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hm0 : m = 0
      · subst m
        refine ⟨2, by norm_num, ?_⟩
        intro circumference h
        dsimp only
        intro c _hc s T _has _hsT _hTb _hshort hcurv t ht x
        simpa only [Nat.zero_add, pow_one] using hcurv t ht x
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hI (i : Fin m) := ih i i.isLt
      choose Ci hCi hCiBound using hI
      let L := 1 + ∑ i : Fin m, (2 : ℝ) ^ (i.val + 1) * Real.sqrt (Ci i)
      have hL : 1 ≤ L := le_add_of_nonneg_right
        (Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (Real.sqrt_nonneg _)))
      have hL0 : 0 ≤ L := zero_le_one.trans hL
      let K := G.K0 + G.K1 + G.K2 + ∑ d ∈ Finset.range (m + 2), Kseq d
      have hKsum : 0 ≤ ∑ d ∈ Finset.range (m + 2), Kseq d :=
        Finset.sum_nonneg (fun d _ => hKseq d)
      have hK : 0 ≤ K := by
        dsimp only [K]
        linarith only [G.nonnegative.1, G.nonnegative.2.1, G.nonnegative.2.2, hKsum]
      have hK0K : G.K0 ≤ K := by
        dsimp only [K]
        linarith only [G.nonnegative.2.1, G.nonnegative.2.2, hKsum]
      have hK1K : G.K1 ≤ K := by
        dsimp only [K]
        linarith only [G.nonnegative.1, G.nonnegative.2.2, hKsum]
      have hK2K : G.K2 ≤ K := by
        dsimp only [K]
        linarith only [G.nonnegative.1, G.nonnegative.2.1, hKsum]
      have hKseqK (d : ℕ) (hd : d ≤ m + 1) : Kseq d ≤ K := by
        have h := Finset.single_le_sum (fun j _ => hKseq j)
          (Finset.mem_range.mpr (by omega : d < m + 2))
        dsimp only [K]
        linarith only [h, G.nonnegative.1, G.nonnegative.2.1, G.nonnegative.2.2]
      let c0 := 256 + 17 * m62C0 K K K
      let A1 := 113 + 10 * K
      let G1 := 2048 + 992 * K + 160000 * K ^ 2
      let c1 := A1 + G1
      let D0 : ℕ → ℝ := fun i => (Nat.factorial (i + 3) : ℝ) * K * L ^ (i + 3) +
        (2 : ℝ) ^ (i + 1) * L ^ 2
      let D1 : ℕ → ℝ := fun i => (2 : ℝ) ^ (i + 2) * D0 i * L +
        (m63JetErrorMassBound i : ℝ) * K * L ^ (i + 3)
      let T0 : ℕ → ℝ := fun i => (2 : ℝ) ^ (i + 1) * L ^ 3
      let coeff : ℕ → ℝ := fun i =>
        if i = 0 then c0 else if i = 1 then c1 else 2 * K + 4 * D1 i + T0 i ^ 2
      have hC0 : 0 ≤ m62C0 K K K := by unfold m62C0; positivity
      have hc0 : 0 ≤ c0 := by dsimp only [c0]; positivity
      have hA1 : 0 ≤ A1 := by dsimp only [A1]; positivity
      have hG1 : 0 ≤ G1 := by dsimp only [G1]; positivity
      have hc1 : 0 ≤ c1 := add_nonneg hA1 hG1
      have hcoeff (i : ℕ) : 0 ≤ coeff i := by
        by_cases hi0 : i = 0
        · simpa only [coeff, if_pos hi0] using hc0
        by_cases hi1 : i = 1
        · simpa only [coeff, if_neg hi0, if_pos hi1] using hc1
        simp only [coeff, if_neg hi0, if_neg hi1]
        dsimp only [D0, D1, T0]
        positivity
      let Alpha : ℝ := ∑ i ∈ Finset.range (m + 1), coeff i
      let W : ℝ := (m : ℝ) + 1 + Alpha
      let Dc : ℝ := 8 * Alpha * W ^ m +
        Alpha * ∑ i ∈ Finset.range (m + 1), W ^ (m - i)
      have hAlpha : 0 ≤ Alpha := Finset.sum_nonneg (fun i _ => hcoeff i)
      have hW : 0 ≤ W := by dsimp only [W]; positivity
      have hDc : 0 ≤ Dc := by
        dsimp only [Dc]
        exact add_nonneg (by positivity)
          (mul_nonneg hAlpha (Finset.sum_nonneg (fun i _ => pow_nonneg hW _)))
      refine ⟨(2 : ℝ) ^ m * (8 * W ^ m + Dc), by positivity, ?_⟩
      intro circumference hcirc
      dsimp only
      intro c hc s T has hsT hTb hshort hcurv t ht x
      let P := G.product circumference hcirc
      let : Fact (0 < circumference) := ⟨hcirc⟩
      let := P.charts.chartedSpace
      let rho := Real.sqrt (t - s)
      have hage : 0 < t - s := sub_pos.mpr ht.1
      have hrho : 0 < rho := Real.sqrt_pos.mpr hage
      have hrho2 : rho ^ 2 = t - s := Real.sq_sqrt hage.le
      have hrho1 : rho ≤ 1 := by
        have hu : t - s ≤ 1 := by linarith only [ht.2, hshort]
        nlinarith only [hrho2, hu, hrho]
      have hrho2pos : 0 < rho ^ 2 := pow_pos hrho 2
      have hrho2le : rho ^ 2 ≤ 1 := pow_le_one₀ hrho.le hrho1
      have hrho4le : rho ^ 4 ≤ 1 := pow_le_one₀ hrho.le hrho1
      let alpha := s + (t - s) / 4
      let beta := (t + T) / 2
      have hsa : s < alpha := by dsimp only [alpha]; linarith only [ht.1]
      have haalpha : a < alpha := has.trans_lt hsa
      have hat : alpha < t := by dsimp only [alpha]; linarith only [ht.1]
      have htbeta : t < beta := by dsimp only [beta]; linarith only [ht.2]
      have hbetaT : beta < T := by dsimp only [beta]; linarith only [ht.2]
      have habeta : alpha < beta := hat.trans htbeta
      have hfull : Icc alpha beta ⊆ Icc a b := fun u hu =>
        ⟨haalpha.le.trans hu.1, hu.2.trans (hbetaT.le.trans hTb)⟩
      have hinner (u : ℝ) (hu : u ∈ Ioo alpha beta) : u ∈ Ioo s T :=
        ⟨hsa.trans hu.1, hu.2.trans hbetaT⟩
      have hcompactP : IsCompact (univ : Set P.charts.Point) := isCompact_univ
      have hlocal := M63.localCurveTheory_of_compact P.flow hcompactP
      obtain ⟨phi, d, hphi, hbij, hpos, _hperiod, hd, _hspace, heq⟩ :=
        hlocal.fixed_relabeling b (has.trans_lt (hsT.trans_le hTb)) le_rfl
          (Icc a b) (Or.inl rfl) c hc alpha beta haalpha habeta
          (hbetaT.le.trans hTb) hfull
      let F' := m63RestrictClosedFlow P.flow alpha beta hfull habeta
      have hd' : M62ShrinkingCurve F' d := m63SmoothRestriction hd alpha beta Subset.rfl habeta
      have hjet (f : ℝ → ℝ → P.charts.Point) (i : ℕ) (u y : ℝ) :
          m63CurvatureJet F' f i u y = m63CurvatureJet P.flow f i u y := by
        induction i generalizing y with
        | zero => rfl
        | succ i ih =>
          change m62SpatialDerivative P.flow f u (fun z => m63CurvatureJet F' f i u z) y =
            m62SpatialDerivative P.flow f u (fun z => m63CurvatureJet P.flow f i u z) y
          rw [show (fun z => m63CurvatureJet F' f i u z) =
            (fun z => m63CurvatureJet P.flow f i u z) from funext ih]
      have hsq (f : ℝ → ℝ → P.charts.Point) (i : ℕ) :
          m63CurvatureJetSquared F' f i = m63CurvatureJetSquared P.flow f i := by
        funext u y
        simp only [m63CurvatureJetSquared, hjet]
        rfl
      have hfreeze (f : ℝ → ℝ → P.charts.Point) (i : ℕ) (u : ℝ) :
          (fun y => m63CurvatureJet P.flow f i u y) =
            (fun y => m63CurvatureJet P.flow (fun z _ => f z u) i u y) := by
        induction i with
        | zero => rfl
        | succ i ih =>
          funext y
          change m62SpatialDerivative P.flow f u (fun z => m63CurvatureJet P.flow f i u z) y =
            m62SpatialDerivative P.flow (fun z _ => f z u) u
              (fun z => m63CurvatureJet P.flow (fun w _ => f w u) i u z) y
          rw [ih]
          rfl
      have hsqfreeze (f : ℝ → ℝ → P.charts.Point) (i : ℕ) (u y : ℝ) :
          m63CurvatureJetSquared P.flow f i u y =
            m63CurvatureJetSquared P.flow (fun z _ => f z u) i u y := by
        dsimp only [m63CurvatureJetSquared]
        rw [congrFun (hfreeze f i u) y]
      have htransport (i : ℕ) (u : ℝ) (hu : u ∈ Ioo alpha beta) (y : ℝ) :
          m63CurvatureJetSquared P.flow c i u y = m63CurvatureJetSquared F' d i u (phi y) := by
        have hslices : (fun z _ : ℝ => c z u) = (fun z _ : ℝ => d (phi z) u) := by
          funext z v
          exact heq u (Ioo_subset_Icc_self hu) z
        have hcomp := M63.smooth_curvatureJetSquared_comp F' d hd'
          (hphi.differentiable (by norm_num)) hpos hu i y
        rw [hsq (fun z v => d (phi z) v) i] at hcomp
        calc
          _ = m63CurvatureJetSquared P.flow (fun z _ => c z u) i u y := hsqfreeze c i u y
          _ = m63CurvatureJetSquared P.flow (fun z _ => d (phi z) u) i u y := by rw [hslices]
          _ = m63CurvatureJetSquared P.flow (fun z v => d (phi z) v) i u y :=
            (hsqfreeze (fun z v => d (phi z) v) i u y).symm
          _ = _ := hcomp
      let R := 8 / rho ^ 2
      have hR : 0 ≤ R := by dsimp only [R]; positivity
      have hcurv' (u : ℝ) (hu : u ∈ Ioo alpha beta) (y : ℝ) :
          m63CurvatureJetSquared F' d 0 u y ≤ R := by
        obtain ⟨z, rfl⟩ := hbij.2 y
        rw [← htransport 0 u hu z]
        apply (hcurv u (hinner u hu) z).trans
        apply (div_le_div_iff₀ (sub_pos.mpr (hinner u hu).1) hrho2pos).mpr
        dsimp only [alpha] at hu
        nlinarith only [hu.1, hrho2]
      have hLower (i : ℕ) (hi : i < m) (u : ℝ) (hu : u ∈ Ioo alpha beta) (y : ℝ) :
          rho ^ (i + 1) * (F'.metric u).tangentNorm (d y u) (m63CurvatureJet F' d i u y) ≤ L := by
        let ii : Fin m := ⟨i, hi⟩
        obtain ⟨z, rfl⟩ := hbij.2 y
        have hb := hCiBound ii circumference hcirc c hc s T has hsT hTb hshort hcurv
          u (hinner u hu) z
        change m63CurvatureJetSquared P.flow c i u z ≤ Ci ii / (u - s) ^ (i + 1) at hb
        rw [htransport i u hu z] at hb
        have hageu : 0 < u - s := sub_pos.mpr (hinner u hu).1
        have hmul := (le_div_iff₀ (pow_pos hageu (i + 1))).mp hb
        have hsmall : rho ^ 2 ≤ 4 * (u - s) := by
          dsimp only [alpha] at hu
          nlinarith only [hu.1, hrho2]
        let q := m63CurvatureJetSquared F' d i u (phi z)
        let v := (F'.metric u).tangentNorm (d (phi z) u) (m63CurvatureJet F' d i u (phi z))
        have hq : 0 ≤ q := ((F'.metric u).toRiemannianMetric.toCore (d (phi z) u)).re_inner_nonneg _
        have hv : v ^ 2 = q := Real.sq_sqrt hq
        have htwo : ((2 : ℝ) ^ (i + 1)) ^ 2 = (4 : ℝ) ^ (i + 1) := by
          rw [← pow_mul, Nat.mul_comm (i + 1) 2, pow_mul]
          norm_num
        have hsquare : (rho ^ (i + 1) * v) ^ 2 ≤
            ((2 : ℝ) ^ (i + 1) * Real.sqrt (Ci ii)) ^ 2 := by
          calc
            _ = (rho ^ 2) ^ (i + 1) * q := by
              rw [mul_pow, hv, ← pow_mul, ← pow_mul]
              congr 2
              omega
            _ ≤ (4 * (u - s)) ^ (i + 1) * q :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hrho2pos.le hsmall _) hq
            _ = (4 : ℝ) ^ (i + 1) * (q * (u - s) ^ (i + 1)) := by rw [mul_pow]; ring
            _ ≤ (4 : ℝ) ^ (i + 1) * Ci ii := mul_le_mul_of_nonneg_left hmul (by positivity)
            _ = _ := by rw [mul_pow, htwo, Real.sq_sqrt (hCi ii)]
        have hnorm : rho ^ (i + 1) * v ≤ (2 : ℝ) ^ (i + 1) * Real.sqrt (Ci ii) := by
          nlinarith only [hsquare,
            mul_nonneg (show 0 ≤ (2 : ℝ) ^ (i + 1) by positivity) (Real.sqrt_nonneg (Ci ii))]
        exact hnorm.trans ((Finset.single_le_sum
          (fun j _ => mul_nonneg (show 0 ≤ (2 : ℝ) ^ (j.val + 1) by positivity)
            (Real.sqrt_nonneg (Ci j))) (Finset.mem_univ ii)).trans
              (le_add_of_nonneg_left zero_le_one))
      have hBounds : CurveEvolutionAmbientBounds P.flow K K K := by
        refine ⟨?_, ?_, ?_⟩
        · intro u hu p v hv
          exact ((G.product_bounds circumference hcirc).riemann u hu p v hv).trans hK0K
        · intro u hu p v hv
          exact ((G.product_bounds circumference hcirc).ricci_derivative u hu p v hv).trans hK1K
        · intro u hu p v w hv hw
          exact ((G.product_bounds circumference hcirc).ricci u hu p v w hv hw).trans hK2K
      have hBounds' : CurveEvolutionAmbientBounds F' K K K :=
        m63RestrictAmbientBounds hBounds alpha beta hfull habeta
      have hqnon (i : ℕ) (u y : ℝ) : 0 ≤ m63CurvatureJetSquared F' d i u y :=
        ((F'.metric u).toRiemannianMetric.toCore (d y u)).re_inner_nonneg _
      have hzero (u : ℝ) (hu : u ∈ Ioo alpha beta) (y : ℝ) :
          deriv (fun r => m63CurvatureJetSquared F' d 0 r y) u -
              m62ArcSecondDerivative F' d u (m63CurvatureJetSquared F' d 0 u) y ≤
            -2 * m63CurvatureJetSquared F' d 1 u y + c0 / rho ^ 4 := by
        have hraw := spatial_squared_bound F' d hd' hK hK hK hBounds' hu y
        have hsplit := spatialDerivative_norm_split F' d hd' hu y
        have hqR : m62CurvatureSquared F' d u y ≤ R := hcurv' u hu y
        have hkR : m62Curvature F' d u y ≤ R + 1 := by
          nlinarith only [curvature_sq F' d u y, hqR, sq_nonneg (m62Curvature F' d u y - 1)]
        have hsum : m62CurvatureSquared F' d u y + m62Curvature F' d u y ≤ 2 * R + 1 := by
          linarith only [hqR, hkR]
        have hq2 : m62CurvatureSquared F' d u y ^ 2 ≤ R ^ 2 :=
          pow_le_pow_left₀ (curvatureSquared_nonneg F' d u y) hqR 2
        have hforce : 4 * R ^ 2 + m62C0 K K K * (2 * R + 1) ≤ c0 / rho ^ 4 := by
          apply (le_div_iff₀ (pow_pos hrho 4)).mpr
          have he : (4 * R ^ 2 + m62C0 K K K * (2 * R + 1)) * rho ^ 4 =
              256 + m62C0 K K K * (16 * rho ^ 2 + rho ^ 4) := by
            dsimp only [R]
            field_simp [hrho.ne']
            ring
          rw [he]
          dsimp only [c0]
          nlinarith only [mul_le_mul_of_nonneg_left hrho2le hC0,
            mul_le_mul_of_nonneg_left hrho4le hC0]
        change m63CurvatureJetSquared F' d 1 u y =
          (F'.metric u).inner (d y u) (m62SpatialNormalDerivative F' d u y)
            (m62SpatialNormalDerivative F' d u y) + m62CurvatureSquared F' d u y ^ 2 at hsplit
        change deriv (fun r => m62CurvatureSquared F' d r y) u -
          m62ArcSecondDerivative F' d u (m62CurvatureSquared F' d u) y ≤ _
        nlinarith only [hraw, hsplit, hq2, hforce, mul_le_mul_of_nonneg_left hsum hC0]
      have hfirst (u : ℝ) (hu : u ∈ Ioo alpha beta) (y : ℝ) :
          deriv (fun r => m63CurvatureJetSquared F' d 1 r y) u -
              m62ArcSecondDerivative F' d u (m63CurvatureJetSquared F' d 1 u) y ≤
            -m63CurvatureJetSquared F' d 2 u y +
              (c1 / rho ^ 2) * m63CurvatureJetSquared F' d 1 u y + c1 / rho ^ 6 := by
        have hraw := m63FirstJetSquared_dissipation_split F' d hd' hK hR hBounds' hu y
          (hcurv' u hu y)
          (fun v hv => ((hTensor circumference P 1 u (hfull (Ioo_subset_Icc_self hu))
            (d y u)).1 v hv).trans (hKseqK 1 (by omega)))
          (fun v hv => ((hTensor circumference P 2 u (hfull (Ioo_subset_Icc_self hu))
            (d y u)).2 v hv).trans (hKseqK 2 (by omega)))
        have hreact : 14 * R + 10 * K + 1 ≤ A1 / rho ^ 2 := by
          apply (le_div_iff₀ hrho2pos).mpr
          have he : (14 * R + 10 * K + 1) * rho ^ 2 = 112 + (10 * K + 1) * rho ^ 2 := by
            dsimp only [R]
            field_simp [hrho.ne']
            ring
          rw [he]
          dsimp only [A1]
          nlinarith only [mul_le_mul_of_nonneg_left hrho2le (show 0 ≤ 10 * K + 1 by positivity)]
        have hforce : 4 * R ^ 3 + 2 * R * K * (7 * R + 6) + (K * (46 * R + 32)) ^ 2 ≤
            G1 / rho ^ 6 := by
          apply (le_div_iff₀ (pow_pos hrho 6)).mpr
          have he : (4 * R ^ 3 + 2 * R * K * (7 * R + 6) + (K * (46 * R + 32)) ^ 2) * rho ^ 6 =
              2048 + 896 * K * rho ^ 2 + 96 * K * rho ^ 4 +
                K ^ 2 * rho ^ 2 * (368 + 32 * rho ^ 2) ^ 2 := by
            dsimp only [R]
            field_simp [hrho.ne']
            ring
          have h400 : 368 + 32 * rho ^ 2 ≤ 400 := by linarith only [hrho2le]
          have hsq400 : (368 + 32 * rho ^ 2) ^ 2 ≤ 160000 := by
            have h := pow_le_pow_left₀ (show 0 ≤ 368 + 32 * rho ^ 2 by positivity) h400 2
            norm_num at h
            exact h
          have hlast : K ^ 2 * rho ^ 2 * (368 + 32 * rho ^ 2) ^ 2 ≤ 160000 * K ^ 2 := by
            calc
              _ ≤ K ^ 2 * rho ^ 2 * 160000 :=
                mul_le_mul_of_nonneg_left hsq400 (mul_nonneg (sq_nonneg K) hrho2pos.le)
              _ ≤ K ^ 2 * 1 * 160000 := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hrho2le (sq_nonneg K)) (by norm_num)
              _ = _ := by ring
          rw [he]
          dsimp only [G1]
          nlinarith only [hlast, mul_le_mul_of_nonneg_left hrho2le hK,
            mul_le_mul_of_nonneg_left hrho4le hK]
        have hAc : A1 / rho ^ 2 ≤ c1 / rho ^ 2 :=
          div_le_div_of_nonneg_right (le_add_of_nonneg_right hG1) hrho2pos.le
        have hGc : G1 / rho ^ 6 ≤ c1 / rho ^ 6 :=
          div_le_div_of_nonneg_right (le_add_of_nonneg_left hA1) (pow_nonneg hrho.le _)
        exact hraw.trans (add_le_add
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hreact.trans hAc) (hqnon 1 u y)))
          (hforce.trans hGc))
      have hpoint (i : ℕ) (hi : i ≤ m) (u : ℝ) (hu : u ∈ Ioo alpha beta) (y : ℝ) :
          deriv (fun r => m63CurvatureJetSquared F' d i r y) u -
              m62ArcSecondDerivative F' d u (m63CurvatureJetSquared F' d i u) y ≤
            -m63CurvatureJetSquared F' d (i + 1) u y +
              (coeff i / rho ^ 2) * m63CurvatureJetSquared F' d i u y +
                coeff i / rho ^ (2 * i + 4) := by
        by_cases hi0 : i = 0
        · subst i
          simp only [coeff, if_pos rfl, Nat.zero_add, Nat.mul_zero]
          have hneg : -2 * m63CurvatureJetSquared F' d 1 u y ≤
              -m63CurvatureJetSquared F' d 1 u y := by
            simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right
              (by norm_num : (-2 : ℝ) ≤ -1) (hqnon 1 u y)
          exact (hzero u hu y).trans (add_le_add
            (hneg.trans (le_add_of_nonneg_right
              (mul_nonneg (div_nonneg hc0 hrho2pos.le) (hqnon 0 u y)))) le_rfl)
        by_cases hi1 : i = 1
        · subst i
          simpa only [coeff, if_neg (by omega : (1 : ℕ) ≠ 0), if_pos rfl,
            if_true, Nat.reduceAdd, Nat.reduceMul] using hfirst u hu y
        have hi2 : 2 ≤ i := by omega
        have hh := (m63CurvatureJetSquared_scaled_dissipation_of_lower_bounds F' d hd' i hi2
          hrho hrho1 hK hL hu y
          (fun j hj => hLower j (lt_of_lt_of_le hj hi) u hu y)
          (fun k hk v hv => ((hTensor circumference P k u (hfull (Ioo_subset_Icc_self hu))
            (d y u)).1 v hv).trans (hKseqK k (by omega)))
          (fun k hk v hv => ((hTensor circumference P k u (hfull (Ioo_subset_Icc_self hu))
            (d y u)).2 v hv).trans (hKseqK k (by omega)))).2
        have hscale : rho ^ (2 * i + 4) *
            (-m63CurvatureJetSquared F' d (i + 1) u y +
              (coeff i / rho ^ 2) * m63CurvatureJetSquared F' d i u y +
                coeff i / rho ^ (2 * i + 4)) =
            -(rho ^ (2 * i + 4) * m63CurvatureJetSquared F' d (i + 1) u y) +
              coeff i * (rho ^ (2 * i + 2) * m63CurvatureJetSquared F' d i u y) + coeff i := by
          have he : rho ^ (2 * i + 4) = rho ^ (2 * i + 2) * rho ^ 2 := by
            rw [← pow_add]
          rw [he]
          field_simp [hrho.ne']
        apply (mul_le_mul_iff_right₀ (pow_pos hrho (2 * i + 4))).mp
        rw [hscale]
        simpa only [coeff, if_neg hi0, if_neg hi1, D0, D1, T0] using hh
      have hdiss : ∀ i ≤ m, ∀ u ∈ Ioo alpha beta, u - alpha ≤ rho ^ 2 → ∀ y,
          deriv (fun r => m63CurvatureJetSquared F' d i r y) u -
              m62ArcSecondDerivative F' d u (m63CurvatureJetSquared F' d i u) y ≤
            -m63CurvatureJetSquared F' d (i + 1) u y +
              (Alpha / rho ^ 2) * m63CurvatureJetSquared F' d i u y +
                (Alpha / rho ^ 4) / (u - alpha) ^ i := by
        intro i hi u hu huH y
        have hcoeffA : coeff i ≤ Alpha := Finset.single_le_sum (fun j _ => hcoeff j)
          (Finset.mem_range.mpr (by omega))
        have hageu : 0 < u - alpha := sub_pos.mpr hu.1
        have hforce : coeff i / rho ^ (2 * i + 4) ≤ (Alpha / rho ^ 4) / (u - alpha) ^ i := by
          rw [div_div]
          apply (div_le_div_iff₀ (pow_pos hrho _) (mul_pos (pow_pos hrho _) (pow_pos hageu _))).mpr
          calc
            _ ≤ Alpha * (rho ^ 4 * (u - alpha) ^ i) :=
              mul_le_mul_of_nonneg_right hcoeffA (by positivity)
            _ ≤ Alpha * (rho ^ 4 * (rho ^ 2) ^ i) := mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hageu.le huH i)
                (pow_nonneg hrho.le _)) hAlpha
            _ = Alpha * rho ^ (2 * i + 4) := by
              rw [← pow_mul, ← pow_add]
              congr 2
              omega
        exact (hpoint i hi u hu y).trans (add_le_add
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hcoeffA hrho2pos.le) (hqnon i u y))) hforce)
      have htH : t - alpha ≤ rho ^ 2 := by
        dsimp only [alpha]
        linarith only [hrho2, hage]
      have htHalf : rho ^ 2 / 2 ≤ t - alpha := by
        dsimp only [alpha]
        linarith only [hrho2, hage]
      have hWexact : (m : ℝ) + 1 + (Alpha / rho ^ 2) * rho ^ 2 = W := by
        rw [div_mul_cancel₀ _ (pow_ne_zero _ hrho.ne')]
      have hDexact : (Alpha / rho ^ 2) * W ^ m * R +
          (Alpha / rho ^ 4) * ∑ i ∈ Finset.range (m + 1), W ^ (m - i) = Dc / rho ^ 4 := by
        dsimp only [Dc, R]
        field_simp [hrho.ne']
      have hfinite := m63CurvatureJetSquared_bound_of_finite_dissipation F' d hd' m
        (A := Alpha / rho ^ 2) (B := Alpha / rho ^ 4) (R := R) (H := rho ^ 2)
        (div_nonneg hAlpha hrho2pos.le) (div_nonneg hAlpha (pow_nonneg hrho.le _)) hR hrho2pos.le
        (fun u hu _ y => hcurv' u hu y) hdiss (phi x) t ⟨hat, htbeta⟩ htH
      rw [hWexact, hDexact] at hfinite
      rw [htransport m t ⟨hat, htbeta⟩ x]
      have hnum : 0 ≤ W ^ m * R + (Dc / rho ^ 4) * rho ^ 2 :=
        add_nonneg (mul_nonneg (pow_nonneg hW m) hR)
          (mul_nonneg (div_nonneg hDc (pow_nonneg hrho.le 4)) hrho2pos.le)
      calc
        _ ≤ (W ^ m * R + (Dc / rho ^ 4) * (t - alpha)) / (t - alpha) ^ m := hfinite
        _ ≤ (W ^ m * R + (Dc / rho ^ 4) * rho ^ 2) / (t - alpha) ^ m :=
          div_le_div_of_nonneg_right
            (add_le_add le_rfl (mul_le_mul_of_nonneg_left htH
              (div_nonneg hDc (pow_nonneg hrho.le _))))
            (pow_nonneg (sub_nonneg.mpr hat.le) _)
        _ ≤ (W ^ m * R + (Dc / rho ^ 4) * rho ^ 2) / (rho ^ 2 / 2) ^ m :=
          div_le_div_of_nonneg_left hnum (pow_pos (half_pos hrho2pos) _)
            (pow_le_pow_left₀ (half_pos hrho2pos).le htHalf _)
        _ = (2 : ℝ) ^ m * (8 * W ^ m + Dc) / (rho ^ 2) ^ (m + 1) := by
          dsimp only [R]
          rw [div_pow, pow_succ]
          field_simp [hrho.ne']
          ring
        _ = (2 : ℝ) ^ m * (8 * W ^ m + Dc) / (t - s) ^ (m + 1) := by rw [hrho2]
  choose C hC hCBound using hbound
  refine ⟨C, hC, ?_⟩
  intro circumference h
  dsimp only
  intro c hc s T has hsT hTb hshort hcurv t ht i x
  exact hCBound i circumference h c hc s T has hsT hTb hshort hcurv t ht x

end PoincareConjecture
