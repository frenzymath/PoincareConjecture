import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CompactInitialJetImage
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.LocalMetricC2Family
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CompactLocalFamilyGluing
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ContinuousDependenceAngularJets
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ArbitraryC2IntrinsicRegularity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem exists_compact_c2_curve_family
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    (hcompact : IsCompact (univ : Set M))
    (Z : Type u) [TopologicalSpace Z] [CompactSpace Z]
    (gamma : Z → ℝ → M)
    (hgamma : Continuous (fun z : Z × ℝ => gamma z.1 z.2))
    (hfirst : Continuous (fun z : Z × ℝ =>
      m63AngularFirstJet (n := n) (gamma z.1) z.2))
    (hsecond : Continuous (fun z : Z × ℝ =>
      m63AngularSecondJet (F.connection a) (gamma z.1) z.2))
    (hperiod : ∀ z, Function.Periodic (gamma z) curvePeriod)
    (hC2 : ∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gamma z))
    (himmersed : ∀ z x, curveVelocity (n := n) (gamma z) x ≠ 0) :
    ∃ T : ℝ, a < T ∧ T ≤ b ∧ ∃ c : Z → ℝ → ℝ → M,
      (∀ z, M63C2ShrinkingCurveOn F (c z) (Icc a T)) ∧
      (∀ z x, c z x a = gamma z x) ∧
      (∀ z, M63IntrinsicRegularityOn F (c z) (Icc a T)) ∧
      Continuous (fun z : (Z × ℝ) × Icc a T => c z.1.1 z.1.2 z.2) ∧
      Continuous (fun z : (Z × ℝ) × Icc a T =>
        m63AngularFirstJet (n := n) (fun x => c z.1.1 x z.2) z.1.2) ∧
      Continuous (fun z : (Z × ℝ) × Icc a T =>
        m63AngularSecondJet (F.connection z.2)
          (fun x => c z.1.1 x z.2) z.1.2) := by
  classical
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · let := hZ
    let c : Z → ℝ → ℝ → M := fun z => isEmptyElim z
    refine ⟨b, hab, le_rfl, c, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun z => isEmptyElim z
    · exact fun z => isEmptyElim z
    · exact fun z => isEmptyElim z
    · exact continuous_of_const (fun p _ => isEmptyElim p.1.1)
    · exact continuous_of_const (fun p _ => isEmptyElim p.1.1)
    · exact continuous_of_const (fun p _ => isEmptyElim p.1.1)
  · let := hZ
    let : Nonempty M := ⟨gamma (Classical.choice hZ) 0⟩
    let : CompactSpace M := isCompact_univ_iff.mp hcompact
    let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
    obtain ⟨N, e, he, hemb, hinj⟩ :=
      exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
    obtain ⟨U, ρ, hU, heU, hρ, hρe, _hmin, _huniq⟩ :=
      exists_smooth_compact_embedded_retraction e hemb he hinj
    obtain ⟨_hspace, hzero, hfirstW, hsecondW⟩ :=
      continuous_embedded_initial_jets F ⟨le_rfl, hab.le⟩ gamma
        hgamma hfirst hsecond hC2 he hU heU hρ hρe
    obtain ⟨J, hK, _hJ, hdata, hzeroK, hfirstK, hsecondK, hrestore⟩ :=
      exists_compact_initialJet_image gamma hperiod hC2 himmersed he hρe
        hzero hfirstW hsecondW
    let W := EuclideanSpace ℝ (Fin N)
    let Y := C(AddCircle curvePeriod, (W × W) × W)
    let K := range (J : Z → Y)
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let gammaK : K → ℝ → M := fun k x =>
      ρ ((k.1 (x : AddCircle curvePeriod)).1.1)
    have hlocal := fun k : K => exists_local_metric_c2_curve_family F hab hcompact
      he hU heU hρ hρe gammaK (fun k => (hdata k).1)
      (fun k => (hdata k).2.1) (fun k => (hdata k).2.2.1)
      hzeroK hfirstK hsecondK k
    obtain ⟨T, haT, hTb, cK, hcK, hcK0, hcKzero, hcKfirst, hcKsecond⟩ :=
      exists_compact_c2_family_of_local_families F hab hcompact gammaK e hlocal
    let j : Z → K := fun z => ⟨J z, mem_range_self z⟩
    have hj : Continuous j := J.continuous.subtype_mk (fun z => mem_range_self z)
    let c : Z → ℝ → ℝ → M := fun z => cK (j z)
    have hc (z : Z) : M63C2ShrinkingCurveOn F (c z) (Icc a T) := hcK (j z)
    have hc0 (z : Z) (x : ℝ) : c z x a = gamma z x :=
      (hcK0 (j z) x).trans (hrestore z x)
    let pull : (Z × ℝ) × Icc a T → (K × ℝ) × Icc a T :=
      fun p => ((j p.1.1, p.1.2), p.2)
    have hpull : Continuous pull :=
      ((hj.comp continuous_fst.fst).prodMk continuous_fst.snd).prodMk continuous_snd
    have hcZero : Continuous (fun p : (Z × ℝ) × Icc a T =>
        e (c p.1.1 p.1.2 p.2)) := hcKzero.comp hpull
    have hcFirst : Continuous (fun p : (Z × ℝ) × Icc a T =>
        deriv (fun x => e (c p.1.1 x p.2)) p.1.2) := hcKfirst.comp hpull
    have hcSecond : Continuous (fun p : (Z × ℝ) × Icc a T =>
        deriv (deriv (fun x => e (c p.1.1 x p.2))) p.1.2) := hcKsecond.comp hpull
    let reorder : (Z × Icc a T) × ℝ → (Z × ℝ) × Icc a T :=
      fun p => ((p.1.1, p.2), p.1.2)
    have hreorder : Continuous reorder := by fun_prop
    obtain ⟨hvalue, hangularFirst, hangularSecond⟩ :=
      continuous_angular_jets_of_embedded_jets F
        (fun p : Z × Icc a T => (p.2 : ℝ))
        (continuous_subtype_val.comp continuous_snd)
        (fun p => ⟨p.2.2.1, p.2.2.2.trans hTb⟩)
        (fun p : Z × Icc a T => fun x => c p.1 x p.2)
        (fun p => (hc p.1).spatial_regular p.2 p.2.2)
        he hU heU hρ hρe
        (hcZero.comp hreorder) (hcFirst.comp hreorder) (hcSecond.comp hreorder)
    let undo : (Z × ℝ) × Icc a T → (Z × Icc a T) × ℝ :=
      fun p => ((p.1.1, p.2), p.1.2)
    have hundo : Continuous undo := by fun_prop
    exact ⟨T, haT, hTb, c, hc, hc0,
      fun z => c2ShrinkingCurve_intrinsic_regularity F hcompact haT hTb
        (Or.inl rfl) (hc z),
      hvalue.comp hundo, hangularFirst.comp hundo, hangularSecond.comp hundo⟩

end PoincareConjecture.M63
