import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.ControlledContraction
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.NullLoopHomotopy
import PoincareConjecture.Proofs.M58.Sec18_4_ContractionContinuity
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.PeriodicC1LoopFamily
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.RawLoopLength










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology unitInterval

universe u v

namespace PoincareConjecture.M63

open Proofs.M58



theorem exists_uniform_close_loop_family_homotopy
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {Z : Type v} [TopologicalSpace Z]
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M)) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ Gamma0 Gamma1 : ContinuousMap Z (C1FreeLoopSpace (M := M)),
        (∀ z (x : LoopCircle),
          g.edist (Gamma1 z x) (Gamma0 z x) < ENNReal.ofReal delta) →
        Gamma0.Homotopic Gamma1 ∧
          ∀ z, IsNullHomotopicLoop (Gamma0 z) → IsNullHomotopicLoop (Gamma1 z) := by
  classical
  obtain ⟨C, U, _B, _hU, _hdiag, _hB, h0, h1, _hfix, hC, _hp, _hq, hsmall⟩ :=
    m60_exists_controlled_local_contraction g hcompact
  obtain ⟨delta, hdelta, hpair⟩ := hsmall 1 zero_lt_one
  refine ⟨delta, hdelta, ?_⟩
  intro Gamma0 Gamma1 hclose
  let gamma0 : Z → ℝ → M := fun z => periodicFreeLoop (Gamma0 z)
  let gamma1 : Z → ℝ → M := fun z => periodicFreeLoop (Gamma1 z)
  have hpairs (z : Z) (x : ℝ) : (gamma1 z x, gamma0 z x) ∈ U := by
    let q : LoopCircle := ⟨angularPoint x, norm_angularPoint x⟩
    have heq (gamma : C1FreeLoopSpace (M := M)) : periodicFreeLoop gamma x = gamma q :=
      gamma.boundary q
    apply (hpair _ _ ?_).1
    change g.edist (periodicFreeLoop (Gamma1 z) x) (periodicFreeLoop (Gamma0 z) x) < _
    rw [heq, heq]
    exact hclose z q
  let beta : (I × Z) → ℝ → M := fun w x => C (w.1, gamma1 w.2 x, gamma0 w.2 x)
  have hregular (w : I × Z) (x : ℝ) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (w.1, gamma1 w.2 x, gamma0 w.2 x) :=
    hC _ ⟨w.1.2, hpairs w.2 x⟩
  have hspace0 (z : Z) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (gamma0 z) :=
    contMDiff_periodicFreeLoop (Gamma0 z)
  have hspace1 (z : Z) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (gamma1 z) :=
    contMDiff_periodicFreeLoop (Gamma1 z)
  have hperiod (w : I × Z) : Function.Periodic (beta w) curvePeriod := by
    intro x
    change C (w.1, periodicFreeLoop (Gamma1 w.2) (x + rampPeriod),
      periodicFreeLoop (Gamma0 w.2) (x + rampPeriod)) = _
    rw [periodic_periodicFreeLoop (Gamma1 w.2), periodic_periodicFreeLoop (Gamma0 w.2)]
  have hspace (w : I × Z) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (beta w) := by
    intro x
    exact (hregular w x).comp x
      (contMDiffAt_const.prodMk ((hspace1 w.2 x).prodMk (hspace0 w.2 x)))
  have hj0 : Continuous (fun w : (I × Z) × ℝ =>
      m63AngularFirstJet (n := 3) (gamma0 w.1.2) w.2) :=
    m63AngularFirstJet_continuous.comp
      ((Gamma0.continuous.comp continuous_fst.snd).prodMk continuous_snd)
  have hj1 : Continuous (fun w : (I × Z) × ℝ =>
      m63AngularFirstJet (n := 3) (gamma1 w.1.2) w.2) :=
    m63AngularFirstJet_continuous.comp
      ((Gamma1.continuous.comp continuous_fst.snd).prodMk continuous_snd)
  have hv0 : Continuous (fun w : (I × Z) × ℝ => gamma0 w.1.2 w.2) :=
    (FiberBundle.continuous_proj LoopAmbient (TangentSpace (𝓡 3))).comp hj0
  have hv1 : Continuous (fun w : (I × Z) × ℝ => gamma1 w.1.2 w.2) :=
    (FiberBundle.continuous_proj LoopAmbient (TangentSpace (𝓡 3))).comp hj1
  have ht : Continuous (fun w : (I × Z) × ℝ => (w.1.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst.fst
  have hinput : Continuous (fun w : (I × Z) × ℝ =>
      ((w.1.1 : ℝ), gamma1 w.1.2 w.2, gamma0 w.1.2 w.2)) :=
    ht.prodMk (hv1.prodMk hv0)
  have hvalue : Continuous (fun w : (I × Z) × ℝ => beta w.1 w.2) :=
    continuous_iff_continuousAt.mpr fun w =>
      (hregular w.1 w.2).continuousAt.comp
        (f := fun v : (I × Z) × ℝ =>
          ((v.1.1 : ℝ), gamma1 v.1.2 v.2, gamma0 v.1.2 v.2))
        hinput.continuousAt
  have htzero : Continuous (fun w : (I × Z) × ℝ =>
      (⟨(w.1.1 : ℝ), 0⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (Bundle.Trivialization.continuous_zeroSection ℝ).comp ht
  have hpairjet : Continuous (fun w : (I × Z) × ℝ =>
      (⟨(gamma1 w.1.2 w.2, gamma0 w.1.2 w.2),
        (curveVelocity (gamma1 w.1.2) w.2, curveVelocity (gamma0 w.1.2) w.2)⟩ :
        TangentBundle ((𝓡 3).prod (𝓡 3)) (M × M))) :=
    (contMDiff_equivTangentBundleProd_symm («I» := 𝓡 3) (I' := 𝓡 3)
      (M := M) (M' := M) (n := 0)).continuous.comp (hj1.prodMk hj0)
  have htinput : Continuous (fun w : (I × Z) × ℝ =>
      (⟨((w.1.1 : ℝ), gamma1 w.1.2 w.2, gamma0 w.1.2 w.2),
        (0, curveVelocity (gamma1 w.1.2) w.2, curveVelocity (gamma0 w.1.2) w.2)⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (ℝ × (M × M)))) :=
    (contMDiff_equivTangentBundleProd_symm («I» := 𝓘(ℝ, ℝ))
      (I' := (𝓡 3).prod (𝓡 3)) (M := ℝ) (M' := M × M) (n := 0)).continuous.comp
        (htzero.prodMk hpairjet)
  have htangent : Continuous (fun w : (I × Z) × ℝ =>
      tangentMap (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
        ⟨((w.1.1 : ℝ), gamma1 w.1.2 w.2, gamma0 w.1.2 w.2),
          (0, curveVelocity (gamma1 w.1.2) w.2, curveVelocity (gamma0 w.1.2) w.2)⟩) :=
    continuous_iff_continuousAt.mpr fun w =>
      (continuousAt_tangentMap_of_contMDiffAt (hregular w.1 w.2)).comp
        htinput.continuousAt
  have hfirst : Continuous (fun w : (I × Z) × ℝ =>
      m63AngularFirstJet (n := 3) (beta w.1) w.2) := by
    apply htangent.congr
    intro w
    have hd0 := (hspace0 w.1.2 w.2).mdifferentiableAt one_ne_zero
    have hd1 := (hspace1 w.1.2 w.2).mdifferentiableAt one_ne_zero
    have hchain := mfderiv_comp_apply
      (f := fun x => ((w.1.1 : ℝ), gamma1 w.1.2 x, gamma0 w.1.2 x)) (g := C) w.2
      ((hregular w.1 w.2).mdifferentiableAt one_ne_zero)
      (mdifferentiableAt_const.prodMk (hd1.prodMk hd0)) (1 : ℝ)
    erw [mfderiv_prodMk mdifferentiableAt_const (hd1.prodMk hd0),
      mfderiv_prodMk hd1 hd0] at hchain
    simp only [mfderiv_const] at hchain
    apply TotalSpace.ext
    · rfl
    · exact heq_of_eq hchain.symm
  obtain ⟨K, hK⟩ := exists_continuous_c1Loop_family_of_periodic beta hperiod hspace hvalue hfirst
  let H : I × Z → C1FreeLoopSpace (M := M) := fun w =>
    if w.1 = 0 then Gamma0 w.2 else if w.1 = 1 then Gamma1 w.2 else K w
  have hH0 (z : Z) : H (0, z) = Gamma0 z := by simp only [H, if_true]
  have hH1 (z : Z) : H (1, z) = Gamma1 z := by simp only [H, one_ne_zero, if_false, if_true]
  have hangular (w : I × Z) (x : ℝ) : periodicFreeLoop (H w) x = beta w x := by
    rcases w with ⟨t, z⟩
    dsimp only [H]
    split_ifs with ht0 ht1
    · subst t
      exact (h0 _ _).symm
    · subst t
      exact (h1 _ (hpairs z x)).symm
    · exact hK _ _
  have hsame (w : I × Z) (q : LoopCircle) :
      H w q = K w q ∧ c1LoopTangent (H w) q = c1LoopTangent (K w) q := by
    obtain ⟨x, _hx, hxq⟩ := exists_angularPoint q
    have hq : (⟨angularPoint x, norm_angularPoint x⟩ : LoopCircle) = q :=
      Subtype.ext hxq
    have heq : periodicFreeLoop (H w) = periodicFreeLoop (K w) :=
      funext fun y => (hangular w y).trans (hK w y).symm
    have hboundary (gamma : C1FreeLoopSpace (M := M)) :
        periodicFreeLoop gamma x = gamma q := by
      change gamma.extension (angularPoint x) = gamma q
      rw [← hq]
      exact gamma.boundary ⟨angularPoint x, norm_angularPoint x⟩
    constructor
    · exact (hboundary (H w)).symm.trans ((congrFun heq x).trans (hboundary (K w)))
    · have hj (gamma : C1FreeLoopSpace (M := M)) :
          m63AngularFirstJet (periodicFreeLoop gamma) x = c1LoopTangent gamma q := by
        simpa only [hq] using m63AngularFirstJet_eq_c1LoopTangent gamma x
      rw [← hj (H w), ← hj (K w), heq]
  have hH : Continuous H := by
    have hcan := (continuous_iff_values_tangents _).mp K.continuous
    apply (continuous_iff_values_tangents H).mpr
    constructor
    · exact hcan.1.congr (fun w => ContinuousMap.ext (fun q => (hsame w q).1.symm))
    · exact hcan.2.congr (fun w => ContinuousMap.ext (fun q => (hsame w q).2.symm))
  let hom : Gamma0.Homotopy Gamma1 :=
    { toFun := H
      continuous_toFun := hH
      map_zero_left := hH0
      map_one_left := hH1 }
  refine ⟨⟨hom⟩, ?_⟩
  intro z hnull
  let p : Path (Gamma0 z) (Gamma1 z) :=
    ⟨⟨fun t => hom (t, z), hom.continuous.comp (continuous_id.prodMk continuous_const)⟩,
      hom.apply_zero z, hom.apply_one z⟩
  exact m59NullLoop_of_path p.symm hnull

end PoincareConjecture.M63
