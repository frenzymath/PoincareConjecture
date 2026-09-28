import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ContinuousSpectralInitialJetEncoder
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CommonAmbientSpectralFamily
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CompactSmoothInitialPool
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CompactPoolInitialCurvatureCap











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {Z : Type w} [MetricSpace Z] [CompactSpace Z]
  {a b L : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle L, W)
local notation "J" => ((X × X) × X) × ℝ
local notation "S" => State ((ℤ × Fin 2) × ι)





theorem exists_local_compact_spectral_pool
    (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (gamma : Z → ℝ → M)
    (hperiod : ∀ z, Function.Periodic (gamma z) L)
    (hC2 : ∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gamma z))
    (himm : ∀ z x, curveVelocity (n := n) (gamma z) x ≠ 0)
    (Q : Z → J) (hQ : Continuous Q)
    (hjets : ∀ z (x : ℝ),
      (Q z).1.1.1 (x : AddCircle L) = e (gamma z x) ∧
      (Q z).1.1.2 (x : AddCircle L) = deriv (fun y => e (gamma z y)) x ∧
      (Q z).1.2 (x : AddCircle L) = deriv (deriv (fun y => e (gamma z y))) x)
    (hspeed : ∀ z x, curveSpeed F (fun y _ => gamma z y) a x = (Q z).2)
    (z0 : Z) (hcenter : (Q z0).2 = 1)
    {Tcap : ℝ} (hTcap : 0 < Tcap) (hTcapb : Tcap < b - a)
    (eps : ℕ → ℝ) (heps : ∀ j, 0 < eps j)
    (heps0 : Tendsto eps atTop (𝓝 0)) :
    let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
    let jet := fun (z : S) (x : AddCircle L) =>
      (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) z x),
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) z x))
    ∃ (A : J →L[ℝ] S) (N : Set Z), IsClosed N ∧ z0 ∈ interior N ∧
      ∃ T : ℝ, ∃ hT : 0 < T, T ≤ Tcap ∧ T ≤ 1 ∧
        ∃ (B : Set S) (u : S → ForcingSpace ((ℤ × Fin 2) × ι) T)
          (P : ℕ → Finset J) (R0 : ℝ),
          let K := Q '' N ∪ ⋃ j, (P j : Set J)
          let q := fun z => initialResponseCurve (L := L) hT.le z (u z)
          IsOpen B ∧ A (Q z0) ∈ B ∧
          ContDiffOn ℝ ∞ (fun z => initialResponseTrace lambda z hT.le (u z)) B ∧
          IsCompact K ∧ A '' K ⊆ B ∧
          (∀ p ∈ K, (1 / 2 : ℝ) < p.2 ∧ p.2 < 3 / 2) ∧
          (∀ p ∈ K, ∀ x : ℝ,
            HasDerivAt (fun y : ℝ => p.1.1.1 (y : AddCircle L))
              (p.1.1.2 (x : AddCircle L)) x ∧
            HasDerivAt (fun y : ℝ => p.1.1.2 (y : AddCircle L))
              (p.1.2 (x : AddCircle L)) x) ∧
          (∀ p ∈ K, ∀ x : ℝ,
            p.1.1.1 (x : AddCircle L) ∈ U ∧
            e (ρ (p.1.1.1 (x : AddCircle L))) = p.1.1.1 (x : AddCircle L) ∧
            mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (p.1.1.1 (x : AddCircle L))
              (p.1.1.2 (x : AddCircle L)) ≠ 0) ∧
          (∀ p ∈ K, ∀ x : ℝ,
            curveSpeed F (fun y _ => ρ (p.1.1.1 (y : AddCircle L))) a x = p.2) ∧
          (∀ p ∈ K, ∀ x : AddCircle L,
            jet (A p) x = (p.1.1.1 x, p.1.1.2 x)) ∧
          (∀ j, (P j).Nonempty) ∧
          (∀ j p, p ∈ P j →
            ContDiff ℝ ∞ (fun x : ℝ => p.1.1.1 (x : AddCircle L)) ∧
            ContDiff ℝ ∞ (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s (A p))) ∧
          (∀ j p, p ∈ P j → ∃ z ∈ N, dist p (Q z) < eps j) ∧
          (∀ j z, z ∈ N → ∃ p, p ∈ P j ∧ dist p (Q z) < eps j) ∧
          1 ≤ R0 ∧
          (∀ p ∈ K, ∀ κ : ℝ, 0 < κ → ∀ x : ℝ,
            m62CurvatureSquared F
              (fun y (_ : ℝ) => ρ (p.1.1.1 ((κ * y : ℝ) : AddCircle L))) a x ≤ R0) ∧
          ContinuousOn (fun z : S × (ℝ × ℝ) => q z.1 z.2.1 z.2.2) (B ×ˢ univ) ∧
          ContinuousOn (fun z : S × (ℝ × ℝ) => deriv (q z.1 z.2.1) z.2.2) (B ×ˢ univ) ∧
          (∀ z ∈ B, ∀ t, Function.Periodic (q z t) L) ∧
          (∀ z ∈ B, ∀ x : ℝ, q z 0 x = (jet z (x : AddCircle L)).1) ∧
          (∀ z ∈ B, ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
            q z t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q z t x) (deriv (q z t) x) ≠ 0) ∧
          ∀ z ∈ B,
            ContDiffAt ℝ ∞ (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s z) 0 →
            ContDiffOn ℝ ∞ (Function.uncurry (q z)) (Icc (0 : ℝ) T ×ˢ univ) ∧
            (∀ t : Icc (0 : ℝ) T, ContDiffAt ℝ ∞
              (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s
                (initialResponseTrace lambda z hT.le (u z) t)) 0) ∧
            (∀ t ∈ Ioo (0 : ℝ) T, ∀ x, HasDerivAt (fun s => q z s x)
              (ambientCurvePrincipal F ρ (a + t) (q z t x) (deriv (q z t) x) •
                  iteratedDeriv 2 (q z t) x +
                ambientCurveLower F e ρ (a + t) (q z t x) (deriv (q z t) x)) t) ∧
            ((∀ x, q z 0 x = e (ρ (q z 0 x))) →
              ∀ t ∈ Icc (0 : ℝ) T, ∀ x, q z t x = e (ρ (q z t x))) := by
  classical
  dsimp only
  have hab : a < b := by linarith only [hTcap, hTcapb]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  obtain ⟨A, hA⟩ := exists_continuous_vectorPeriodic_initialJet_encoder (L := L) (ι := ι)
  let f : Z → ℝ → W := fun z x => e (gamma z x)
  have hf (z : Z) : ContDiff ℝ 2 (f z) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp (hC2 z)).contDiff
  have hQder (z : Z) (x : ℝ) :
      HasDerivAt (fun y : ℝ => (Q z).1.1.1 (y : AddCircle L))
          ((Q z).1.1.2 (x : AddCircle L)) x ∧
        HasDerivAt (fun y : ℝ => (Q z).1.1.2 (y : AddCircle L))
          ((Q z).1.2 (x : AddCircle L)) x := by
    have h0 : (fun y : ℝ => (Q z).1.1.1 (y : AddCircle L)) = f z :=
      funext fun y => (hjets z y).1
    have h1 : (fun y : ℝ => (Q z).1.1.2 (y : AddCircle L)) = deriv (f z) :=
      funext fun y => (hjets z y).2.1
    constructor
    · rw [h0, (hjets z x).2.1]
      exact ((hf z).differentiable (by norm_num) x).hasDerivAt
    · rw [h1, (hjets z x).2.2]
      exact (((hf z).deriv' (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have hproject (z : Z) (x : ℝ) :
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f z x) (deriv (f z) x) =
        curveVelocity (n := n) (gamma z) x := by
    have hv : curveVelocity (n := n) (fun y => ρ (f z y)) x =
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f z x) (deriv (f z) x) := by
      change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ f z) x) 1 = _
      erw [mfderiv_comp x
        ((hρ.contMDiffAt (hU.mem_nhds (heU (mem_range_self _)))).mdifferentiableAt (by simp))
        (((hf z).contMDiff x).mdifferentiableAt (by norm_num)),
        ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
      rfl
    have hid : (fun y => ρ (f z y)) = gamma z := funext fun y => hρe (gamma z y)
    rw [hid] at hv
    exact hv.symm
  have hQguard (z : Z) (x : ℝ) :
      (Q z).1.1.1 (x : AddCircle L) ∈ U ∧
        e (ρ ((Q z).1.1.1 (x : AddCircle L))) = (Q z).1.1.1 (x : AddCircle L) ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ ((Q z).1.1.1 (x : AddCircle L))
          ((Q z).1.1.2 (x : AddCircle L)) ≠ 0 := by
    rw [(hjets z x).1, (hjets z x).2.1]
    refine ⟨heU (mem_range_self _), by rw [hρe], ?_⟩
    rw [hproject]
    exact himm z x
  have hQspeed (z : Z) (x : ℝ) :
      curveSpeed F (fun y _ => ρ ((Q z).1.1.1 (y : AddCircle L))) a x = (Q z).2 := by
    have heq : (fun (y : ℝ) (_ : ℝ) => ρ ((Q z).1.1.1 (y : AddCircle L))) =
        fun (y : ℝ) (_ : ℝ) => gamma z y := by
      funext y t
      rw [(hjets z y).1, hρe]
    rw [heq]
    exact hspeed z x
  let E : (ι → ℝ) ≃L[ℝ] W := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let jet : S → AddCircle L → W × W := fun z x =>
    (E (vectorPeriodicJet (L := L) 1 0 (by omega) z x),
      E (vectorPeriodicJet (L := L) 1 1 (by omega) z x))
  have hQjet (z : Z) (x : AddCircle L) :
      jet (A (Q z)) x = ((Q z).1.1.1 x, (Q z).1.1.2 x) :=
    Prod.ext ((hA (Q z) (hQder z)).1 x).1 ((hA (Q z) (hQder z)).1 x).2
  let K0 := range (jet (A (Q z0)))
  have hK0 : IsCompact K0 := isCompact_range
    ((E.continuous.comp (vectorPeriodicJet (L := L) 1 0 (by omega) (A (Q z0))).continuous).prodMk
      (E.continuous.comp (vectorPeriodicJet (L := L) 1 1 (by omega) (A (Q z0))).continuous))
  have hK0sub : K0 ⊆ {z : W × W |
      z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0} := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hQjet]
    exact ⟨(hQguard z0 y).1, (hQguard z0 y).2.2⟩
  have hprincipal (x : AddCircle L) :
      ambientCurvePrincipal F ρ a (jet (A (Q z0)) x).1 (jet (A (Q z0)) x).2 = 1 := by
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hQjet, (hjets z0 y).1, (hjets z0 y).2.1]
    unfold ambientCurvePrincipal
    rw [hproject]
    change ((F.metric a).inner (ρ (e (gamma z0 y)))
      (curveVelocity (gamma z0) y) (curveVelocity (gamma z0) y))⁻¹ = 1
    rw [hρe, ← M62.speed_sq F (fun x _ => gamma z0 x) a y, hspeed, hcenter]
    norm_num
  obtain ⟨T, hT, hTTcap, hT1, B, u, hB, hAB, hpath,
      hqc, hqxc, hqp, hqzero, hqguard, hqflow⟩ :=
    exists_common_ambient_spectral_family F he hU heU hρ hρe hK0 hK0sub
      (A (Q z0)) hTcap hTcapb (fun x => mem_range_self x) hprincipal
  let O : Set J := A ⁻¹' B ∩ (Prod.snd : J → ℝ) ⁻¹' Ioo (1 / 2) (3 / 2)
  have hO : IsOpen O := (hB.preimage A.continuous).inter (isOpen_Ioo.preimage continuous_snd)
  have hzO : Q z0 ∈ O := by
    refine ⟨hAB, ?_⟩
    change (1 / 2 : ℝ) < (Q z0).2 ∧ (Q z0).2 < 3 / 2
    rw [hcenter]
    constructor <;> norm_num
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp ((hO.preimage hQ).mem_nhds hzO)
  let N : Set Z := Metric.closedBall z0 (r / 2)
  have hNclosed : IsClosed N := Metric.isClosed_closedBall
  have hzNint : z0 ∈ interior N := Metric.ball_subset_interior_closedBall
    (Metric.mem_ball_self (half_pos hr))
  have hNO : ∀ z ∈ N, Q z ∈ O := fun z hz =>
    hrsub ((Metric.closedBall_subset_ball (half_lt_self hr)) hz)
  let : CompactSpace N := isCompact_iff_compactSpace.mp hNclosed.isCompact
  let : Nonempty N := ⟨⟨z0, interior_subset hzNint⟩⟩
  let QN : N → J := fun z => Q z
  obtain ⟨P, hPne, hPactual, hPnear, hPcover, hKcompact, hKO⟩ :=
    exists_compact_smooth_initial_pool F ha he hU heU hρ hρe
      (fun z : N => gamma z) (fun z => hperiod z) (fun z => hC2 z)
      (fun z => himm z) QN (hQ.comp continuous_subtype_val)
      (fun z => hjets z) (fun z => hspeed z) hO
      (by rintro _ ⟨z, rfl⟩; exact hNO z z.property) eps heps heps0
  have hQN : range QN = Q '' N := by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  rw [hQN] at hKcompact hKO
  let K : Set J := Q '' N ∪ ⋃ j, (P j : Set J)
  have hKder (p : J) (hp : p ∈ K) (x : ℝ) :
      HasDerivAt (fun y : ℝ => p.1.1.1 (y : AddCircle L))
          (p.1.1.2 (x : AddCircle L)) x ∧
        HasDerivAt (fun y : ℝ => p.1.1.2 (y : AddCircle L))
          (p.1.2 (x : AddCircle L)) x := by
    rcases hp with ⟨z, _hz, rfl⟩ | hp
    · exact hQder z x
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hp
      exact (hPactual j p hj).2.2.2.2.2.1 x
  have hKguard (p : J) (hp : p ∈ K) (x : ℝ) :
      p.1.1.1 (x : AddCircle L) ∈ U ∧
        e (ρ (p.1.1.1 (x : AddCircle L))) = p.1.1.1 (x : AddCircle L) ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (p.1.1.1 (x : AddCircle L))
          (p.1.1.2 (x : AddCircle L)) ≠ 0 := by
    rcases hp with ⟨z, _hz, rfl⟩ | hp
    · exact hQguard z x
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hp
      have hfix := (hPactual j p hj).2.2.2.1 x
      have himm' := (hPactual j p hj).2.2.2.2.1 x
      rw [((hPactual j p hj).2.2.2.2.2.1 x).1.deriv] at himm'
      exact ⟨hfix.1, hfix.2, himm'⟩
  have hKspeed (p : J) (hp : p ∈ K) (x : ℝ) :
      curveSpeed F (fun y _ => ρ (p.1.1.1 (y : AddCircle L))) a x = p.2 := by
    rcases hp with ⟨z, _hz, rfl⟩ | hp
    · exact hQspeed z x
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hp
      exact (hPactual j p hj).2.2.2.2.2.2 x
  obtain ⟨R0, hR0, hcap⟩ := exists_compact_pool_initial_curvature_bound
    F ha he hU heU hρ hρe hKcompact hKder
      (fun p hp x => ⟨(hKguard p hp x).1, (hKguard p hp x).2.2⟩)
      (fun p hp x => (hKguard p hp x).2.1.symm)
  refine ⟨A, N, hNclosed, hzNint, T, hT, hTTcap, hT1, B, u, P, R0,
    hB, hAB, hpath, hKcompact, ?_, ?_, hKder, hKguard, hKspeed, ?_,
    hPne, ?_, ?_, ?_, hR0, hcap, hqc, hqxc, hqp, hqzero, hqguard, hqflow⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (hKO hp).1
  · intro p hp
    exact (hKO hp).2
  · intro p hp x
    exact Prod.ext ((hA p (hKder p hp)).1 x).1 ((hA p (hKder p hp)).1 x).2
  · intro j p hp
    have hpK : p ∈ K := Or.inr (mem_iUnion.mpr ⟨j, hp⟩)
    exact ⟨(hPactual j p hp).2.1, (hA p (hKder p hpK)).2 (hPactual j p hp).2.1⟩
  · intro j p hp
    obtain ⟨z, hz⟩ := hPnear j p hp
    exact ⟨z, z.property, hz⟩
  · intro j z hz
    exact hPcover j ⟨z, hz⟩

end PoincareConjecture.M63
