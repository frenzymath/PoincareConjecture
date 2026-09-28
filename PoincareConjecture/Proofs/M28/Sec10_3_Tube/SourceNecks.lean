import PoincareConjecture.Proofs.M28.Sec10_3_Tube.Claim10_4Trimming
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SliceCover
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundUniformScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CanonicalCarrierUnion











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M28




theorem exists_claim10_4_compact_exclusion_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (F : GeneralizedRicciFlowData.{u}) (time epsilon C Q : ℝ),
        epsilon ≤ epsilon₀ → 0 < C → 0 < Q →
        ∀ (γ : ℝ → (F.slice time).carrier) (a b : ℝ), a ≤ b →
          ContinuousOn γ (Icc a b) →
          F.scalar ⟨time, γ a⟩ ≤ 8 * Q →
          32 * (max C 2) ^ 2 * Q < F.scalar ⟨time, γ b⟩ →
          (∀ N : SingularCComponent (F.metric time) (F.connection time) C,
            Disjoint (γ '' Icc a b) N.carrier) ∧
          ∀ N : SingularRoundComponent (F.metric time) epsilon,
            Disjoint (γ '' Icc a b) N.carrier := by
  obtain ⟨epsilon₀, hepsilon₀, hthreshold, hround⟩ :=
    tube.exists_round_scalar_ratio_accuracy.{u}
  refine ⟨epsilon₀, hepsilon₀, hthreshold, ?_⟩
  intro F time epsilon C Q hsmall hC hQ γ a b hab hγ hstart hend
  let B := max C 2
  have hB : 2 ≤ B := le_max_right C 2
  have hCB : C ≤ B := le_max_left C 2
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hBsquare : B ≤ B ^ 2 := by nlinarith [sq_nonneg (B - 1)]
  have hBsquareQ : B * Q ≤ B ^ 2 * Q :=
    mul_le_mul_of_nonneg_right hBsquare hQ.le
  have hBQ : 0 < B * Q := mul_pos hBpos hQ
  have hCstart : C * F.scalar ⟨time, γ a⟩ ≤ 8 * B * Q := by
    calc
      C * F.scalar ⟨time, γ a⟩ ≤ C * (8 * Q) :=
        mul_le_mul_of_nonneg_left hstart hC.le
      _ ≤ B * (8 * Q) := mul_le_mul_of_nonneg_right hCB (by positivity)
      _ = 8 * B * Q := by ring
  have hend' : 32 * B ^ 2 * Q < F.scalar ⟨time, γ b⟩ := hend
  have hCratio : C * F.scalar ⟨time, γ a⟩ < 6 * F.scalar ⟨time, γ b⟩ := by
    nlinarith only [hCstart, hBsquareQ, hBQ, hend']
  have hQle : 2 * Q ≤ B * Q := mul_le_mul_of_nonneg_right hB hQ.le
  have hroundRatio : 2 * F.scalar ⟨time, γ a⟩ < F.scalar ⟨time, γ b⟩ := by
    nlinarith only [hstart, hQ, hQle, hBsquareQ, hend']
  constructor
  · intro N
    apply disjoint_left.mpr
    rintro x ⟨s, hs, rfl⟩ hsN
    exact F.not_singularCComponent_on_path P time C hab γ hγ hCratio hs N hsN
  · intro N
    apply disjoint_left.mpr
    rintro x ⟨s, hs, rfl⟩ hsN
    have hsubset : γ '' Icc a b ⊆ N.carrier := by
      rw [N.component_eq] at hsN ⊢
      rw [connectedComponent_eq hsN]
      exact (isPreconnected_Icc.image γ hγ).subset_connectedComponent
        (mem_image_of_mem γ hs)
    have hratio := hround (F.slice time).carrier (F.metric time) (F.connection time)
      epsilon N hsmall (γ b) (hsubset (mem_image_of_mem γ (right_mem_Icc.mpr hab)))
      (γ a) (hsubset (mem_image_of_mem γ (left_mem_Icc.mpr hab)))
    exact (not_lt_of_ge hratio) hroundRatio





theorem exists_claim10_4_source_necks_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (F : GeneralizedRicciFlowData.{u}) (time epsilon C Q : ℝ),
        0 < epsilon → epsilon ≤ epsilon₀ → 0 < C → 0 < Q →
        ∀ (H : ConnectedNeckCapCover (F.metric time)),
          H.epsilon = epsilon → H.cap_constant = C →
          ∀ (component_base : (F.slice time).carrier) (U : Set (F.slice time).carrier)
            (γ : ℝ → (F.slice time).carrier) (a b : ℝ), a ≤ b →
            H.X = connectedComponentIn {p | 4 * Q < F.scalar ⟨time, p⟩}
              component_base →
            H.X ⊆ U → U ⊆ H.canonicalCarrierUnion →
            ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b) →
            MapsTo γ (Icc a b) U →
            (F.metric time).pathELength γ a b ≠ ⊤ →
            (F.metric time).pathELength γ a b =
              intrinsicEDist (F.metric time) U (γ a) (γ b) →
            F.scalar ⟨time, γ a⟩ ≤ 8 * (max C 2) * Q →
            32 * (max C 2) ^ 3 * Q < F.scalar ⟨time, γ b⟩ →
            generalizedSliceStrongCanonicalNeighborhoods F epsilon C (4 * Q) time →
            ∃ s t : ℝ, a < s ∧ s < t ∧ t < b ∧
              F.scalar ⟨time, γ s⟩ = 16 * (max C 2) ^ 2 * Q ∧
              F.scalar ⟨time, γ t⟩ = F.scalar ⟨time, γ b⟩ / (2 * (max C 2)) ∧
              (∀ v ∈ Icc s t, F.scalar ⟨time, γ v⟩ ∈
                Icc (16 * (max C 2) ^ 2 * Q)
                  (F.scalar ⟨time, γ b⟩ / (2 * (max C 2)))) ∧
              (F.metric time).pathELength γ s t ≤ (F.metric time).pathELength γ a b ∧
              ∃ hhalf : epsilon < 1 / 2, ∃ K : NeckOnlyCover (F.metric time),
                K.X = γ '' Icc s t ∧ K.epsilon = epsilon ∧
                K.X ⊆ H.X ∧
                (∀ N ∈ K.necks, ∃ S : GeneralizedStrongNeck F time epsilon,
                  N = strongNeck_top S hhalf ∧ S.center ∈ K.X) ∧
                ∀ v ∈ Icc s t, ∃ S : GeneralizedStrongNeck F time epsilon,
                  S.center = γ v := by
  obtain ⟨epsilonC, hCpos, hCthreshold, hcompact⟩ :=
    exists_claim10_4_compact_exclusion_accuracy P
  obtain ⟨epsilonU, hUpos, _, hcapture⟩ :=
    exists_canonicalCarrierUnion_scalar_accuracy.{u}
  let epsilon₀ := min epsilonC (min epsilonU neckShorteningEpsilon)
  have hpos : 0 < epsilon₀ :=
    lt_min hCpos (lt_min hUpos neckShorteningEpsilon_pos)
  have hthreshold : epsilon₀ ≤ (1 / 200 : ℝ) :=
    (min_le_left _ _).trans hCthreshold
  refine ⟨epsilon₀, hpos, hthreshold, ?_⟩
  intro F time epsilon C Q hepsilon hsmall hC hQ H hHepsilon hHC component_base U γ a b hab
    hHX hXU hUV hγ hγU hfinite hmin hstart hend hcanonical
  have hsmallC : epsilon ≤ epsilonC := hsmall.trans (min_le_left _ _)
  have hsmallU : epsilon ≤ epsilonU :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hshort : epsilon ≤ neckShorteningEpsilon :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hhalf : epsilon < 1 / 2 :=
    lt_of_le_of_lt (hsmall.trans hthreshold) (by norm_num)
  have hB : 2 ≤ max C 2 := le_max_right C 2
  have hBQ : 0 < max C 2 * Q := mul_pos (lt_of_lt_of_le (by norm_num) hB) hQ
  have hQle : Q ≤ max C 2 * Q := by
    nlinarith only [mul_le_mul_of_nonneg_right hB hQ.le, hQ]
  have hstart' : F.scalar ⟨time, γ a⟩ ≤ 8 * (max C 2 * Q) := by
    simpa only [mul_assoc] using hstart
  have hend' : 32 * (max C 2) ^ 2 * (max C 2 * Q) < F.scalar ⟨time, γ b⟩ := by
    convert hend using 1
    ring
  obtain ⟨hcomponent, hround⟩ := hcompact F time epsilon C (max C 2 * Q)
    hsmallC hC hBQ γ a b hab hγ.continuousOn hstart' hend'
  have hscalar : ContinuousOn (fun v => F.scalar ⟨time, γ v⟩) (Icc a b) :=
    (F.continuous_scalar_slice P time).comp_continuousOn hγ.continuousOn
  obtain ⟨s, t, has, hst, htb, hsvalue, htvalue, hband⟩ :=
    exists_claim10_4_scalar_band hab hscalar hB hBQ hstart' hend'
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has.le htb.le
  have hretained (v : ℝ) (hv : v ∈ Icc s t) : γ v ∈ H.X := by
    apply hcapture (F.slice time).carrier (F.metric time) (F.connection time)
      H Q component_base hQ (by simpa only [hHepsilon] using hsmallU) hHX (γ v)
      (hUV (hγU (hsub hv)))
    rw [hHC]
    change 8 * (max C 2) * Q ≤ F.scalar ⟨time, γ v⟩
    have hlow := (hband v hv).1
    nlinarith only [hlow, hBQ, mul_le_mul_of_nonneg_right hB hBQ.le]
  have hcapfree (v : ℝ) (hv : v ∈ Icc s t)
      (N : CapCertificate (F.metric time)) (hNepsilon : N.epsilon = epsilon)
      (hNC : N.cap_constant ≤ C) : γ v ∉ N.core := by
    have hcomponentU : connectedComponentIn
        {p | 4 * (max C 2 * Q) < (F.connection time).scalarCurvature p} (γ v) ⊆ U := by
      have hcomp := connectedComponentIn_eq (hHX ▸ hretained v hv)
      have hmono : {p | 4 * (max C 2 * Q) < F.scalar ⟨time, p⟩} ⊆
          {p | 4 * Q < F.scalar ⟨time, p⟩} := by
        intro p hp
        change 4 * (max C 2 * Q) < F.scalar ⟨time, p⟩ at hp
        change 4 * Q < F.scalar ⟨time, p⟩
        linarith only [hp, hQle]
      apply (connectedComponentIn_mono (γ v) hmono).trans
      rw [← hcomp, ← hHX]
      exact hXU
    exact N.not_mem_core_of_scalar_band (F.connection time)
      (by simpa only [hNepsilon] using hshort) (hNC.trans (le_max_left C 2)) hBQ
      (hsub hv) hγ hγU hfinite hmin hcomponentU hstart' (hband v hv).1 (hband v hv).2
  have hX : IsConnected (γ '' Icc s t) :=
    (isConnected_Icc hst.le).image γ (hγ.continuousOn.mono hsub)
  have hcan : ∀ x ∈ γ '' Icc s t,
      Nonempty (GeneralizedCanonicalControl (F := F) time x epsilon C) := by
    rintro x ⟨v, hv, rfl⟩
    apply hcanonical
    have hlow := (hband v hv).1
    have hbase : 4 * Q ≤ 16 * (max C 2) * (max C 2 * Q) := by
      nlinarith only [hQle, hBQ, mul_le_mul_of_nonneg_right hB hBQ.le]
    exact hbase.trans hlow
  have hcomponent' (N : SingularCComponent (F.metric time) (F.connection time) C) :
      Disjoint (γ '' Icc s t) N.carrier := by
    apply disjoint_left.mpr
    rintro x ⟨v, hv, rfl⟩ hxN
    exact disjoint_left.mp (hcomponent N) (mem_image_of_mem γ (hsub hv)) hxN
  have hround' (N : SingularRoundComponent (F.metric time) epsilon) :
      Disjoint (γ '' Icc s t) N.carrier := by
    apply disjoint_left.mpr
    rintro x ⟨v, hv, rfl⟩ hxN
    exact disjoint_left.mp (hround N) (mem_image_of_mem γ (hsub hv)) hxN
  let T := testedSliceNeckCapCover hepsilon hsmall hthreshold hC
    (γ '' Icc s t) hX hcan hcomponent' hround'
  have hcenters : ∀ x ∈ T.X, ∃ N, N ∈ T.necks ∧ N.center = x := by
    intro x hx
    rcases T.pointwise_cover x hx with hneck | ⟨N, hN, hxcore⟩
    · exact hneck
    · obtain ⟨v, hv, rfl⟩ := hx
      exact False.elim (hcapfree v hv N (T.cap_epsilon N hN)
        (T.cap_constant_bound N hN) hxcore)
  let K : NeckOnlyCover (F.metric time) := {
    epsilon := T.epsilon
    epsilon_pos := T.epsilon_pos
    epsilon_threshold := T.epsilon_threshold
    epsilon_threshold_pos := T.epsilon_threshold_pos
    epsilon_threshold_le_one_two_hundred := T.epsilon_threshold_le_one_two_hundred
    epsilon_le_threshold := T.epsilon_le_threshold
    X := T.X
    connected_X := T.connected_X
    necks := T.necks
    pointwise_center_cover := hcenters
    neck_epsilon := T.neck_epsilon }
  have hprovenance (N : EpsilonNeck (F.metric time)) (hN : N ∈ K.necks) :
      ∃ S : GeneralizedStrongNeck F time epsilon,
        N = strongNeck_top S hhalf ∧ S.center ∈ K.X := by
    exact testedSliceNeckCapCover_neck_provenance hepsilon hsmall hthreshold hC
      (γ '' Icc s t) hX hcan hcomponent' hround' N hN
  have hloweq : 16 * (max C 2) * (max C 2 * Q) = 16 * (max C 2) ^ 2 * Q := by ring
  rw [hloweq] at hsvalue hband
  refine ⟨s, t, has, hst, htb, hsvalue, htvalue, hband, ?_, hhalf, K, rfl, rfl,
    ?_, hprovenance, ?_⟩
  · let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : (F.slice time).carrier → Type _) :=
      ⟨(F.metric time).toRiemannianMetric⟩
    exact Manifold.pathELength_mono has.le htb.le
  · rintro x ⟨v, hv, rfl⟩
    exact hretained v hv
  · intro v hv
    obtain ⟨N, hN, hcenter⟩ := K.pointwise_center_cover (γ v) (mem_image_of_mem γ hv)
    obtain ⟨S, htop, _⟩ := hprovenance N hN
    refine ⟨S, ?_⟩
    simpa only [htop, strongNeck_top] using hcenter

end PoincareConjecture.M28
