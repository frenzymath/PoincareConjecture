import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeJointCylinder
import PoincareConjecture.Proofs.M76.Triangulation.TerminalHeightRegionBalls
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLGraphCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.SmallSupportedPLDeformation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInteriorChart
import PoincareConjecture.Proofs.M76.Mathlib.ClosedExtension
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalTransport












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



def cylinderSlice {D : Set (E × ℝ)} (e : D ≃ₜ D) (d : Set E) (t : ℝ) :
    Set (E × ℝ) :=
  {z | ∃ p : D, (p : E × ℝ).1 ∈ d ∧ (p : E × ℝ).2 = t ∧ (e p : E × ℝ) = z}




def HasPairedHeightCap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S C d : Set F) (A : F → ℝ) (c : ℝ) : Prop :=
  ∃ B : Set F,
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B (d ∪ (S ∩ {x | A x ≤ c})) ∧
    B ⊆ interior C ∧ B ⊆ {x | A x ≤ c} ∧
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior B ×ˢ {1})
      ((d ∪ (S ∩ {x | A x ≤ c})) ×ˢ {(1 : ℝ)})






theorem exists_paired_height_cap_step
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hcv : Convex ℝ K.space)
    {r : ℝ} (hr : 0 < r)
    (e : (K.space ×ˢ Icc (-r) r : Set (E × ℝ)) ≃ₜ (K.space ×ˢ Icc (-r) r))
    (he : e.IsFinitePL)
    (hheight : ∀ p, (e p : E × ℝ).2 = (p : E × ℝ).2)
    (hstart : ∀ p : (K.space ×ˢ Icc (-r) r : Set (E × ℝ)),
      (p : E × ℝ).2 = 0 → e p = p)
    {S C : Set (E × ℝ)} {d q : Set E}
    (hd : IsCompact d) (hdK : d ⊆ interior K.space)
    (hdC : ∀ x ∈ d, (x, (0 : ℝ)) ∈ interior C) (hqd : q ⊆ d)
    (hsection : ∀ p, (e p : E × ℝ) ∈ S ↔ (p : E × ℝ).1 ∈ q)
    (hband : S ∩ {p | p.2 ∈ Icc (-r) r} ⊆ K.space ×ˢ Icc (-r) r) :
    ∃ ε : ℝ, 0 < ε ∧ ε < r ∧
      ∀ a b : ℝ, |a| ≤ ε → |b| ≤ ε → a ≤ b →
        HasPairedHeightCap S C (cylinderSlice e d a) Prod.snd a →
          HasPairedHeightCap S C (cylinderSlice e d b) Prod.snd b := by
  classical
  let D : Set (E × ℝ) := K.space ×ˢ Icc (-r) r
  have hDcompact : IsCompact D := (K.isCompact_space_of_finite hK).prod isCompact_Icc
  have hDcv : Convex ℝ D := hcv.prod (convex_Icc (-r) r)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show -r < r by linarith)
  obtain ⟨R, hR, hRprod, _⟩ := K.exists_finite_triangulation_prod J hK hJ
  have hRD : R.space = D := by rw [hRprod, hJI]
  obtain ⟨H, hHS, _, _, _, _, _, hHe, _⟩ := he.exists_interior_chart rfl
  let U : Set (E × ℝ) := H.source ∩ H ⁻¹' interior C
  have hU : IsOpen U := H.isOpen_inter_preimage isOpen_interior
  have hUinside : U ⊆ interior D := by
    intro p hp
    exact hHS.subset hp.1
  have hbase : d ×ˢ {(0 : ℝ)} ⊆ U := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht0 : t = 0 := mem_singleton_iff.mp ht
    subst t
    have hpD : (x, (0 : ℝ)) ∈ D :=
      ⟨interior_subset (hdK hx), by constructor <;> linarith⟩
    refine ⟨?_, ?_⟩
    · rw [hHS]
      change (x, (0 : ℝ)) ∈ interior (K.space ×ˢ Icc (-r) r)
      rw [interior_prod_eq, interior_Icc]
      exact ⟨hdK hx, by constructor <;> linarith⟩
    · change H (x, (0 : ℝ)) ∈ interior C
      rw [hHe ⟨(x, 0), hpD⟩, hstart ⟨(x, 0), hpD⟩ rfl]
      exact hdC x hx
  obtain ⟨u, v, _, hv, hdu, h0v, huv⟩ :=
    generalized_tube_lemma hd isCompact_singleton hU hbase
  obtain ⟨η, hη, hηv⟩ := Metric.isOpen_iff.mp hv 0 (h0v (mem_singleton 0))
  have hstrip : d ×ˢ Icc (-η / 2) (η / 2) ⊆ U := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    apply huv
    refine ⟨hdu hx, hηv ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have habs : |t| ≤ η / 2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    exact habs.trans_lt (by linarith)
  obtain ⟨g, L, hL, hLU, hg, hgunit, hgoff, hgcont, _, hgbound, _⟩ :=
    SimplicialComplex.exists_locallyPL_supported_graph_extension
      (hd.prod isCompact_Icc) hU hstrip
  let σ : E × ℝ → ℝ := fun p => (g p).1
  have hσL : FinitePiecewiseAffineOn σ L.space :=
    hg.postcomp (ContinuousLinearMap.fst ℝ ℝ (E × ℝ)).toContinuousAffineMap
  have hσoff (p : E × ℝ) (hp : p ∉ L.space) : σ p = 0 := by
    dsimp [σ]
    rw [hgoff p hp]
    rfl
  have hσD : FinitePiecewiseAffineOn σ D := by
    rw [← hRD]
    exact hσL.on_finite_polyhedron_of_eq_affine_off hgcont.fst
      (ContinuousAffineMap.const ℝ (E × ℝ) (0 : ℝ)) hσoff R hR
  let f : E × ℝ → E × ℝ := fun p => (0, σ p)
  have hf : FinitePiecewiseAffineOn f D := by
    have hz : FinitePiecewiseAffineOn (fun _ : E × ℝ => (0 : E)) D := by
      rw [← hRD]
      exact (R.affineOnFaces_affine
        (ContinuousAffineMap.const ℝ (E × ℝ) (0 : E))).finitePiecewiseAffineOn hR
    exact hz.prod_mk hσD
  have hfzero (p : E × ℝ) (hp : p ∈ frontier D) : f p = 0 := by
    have hpL : p ∉ L.space := fun h => hp.2 (hUinside (hLU h))
    simp only [f, hσoff p hpL, Prod.mk_zero_zero]
  obtain ⟨ε₀, hε₀, hsmall⟩ := hf.exists_small_supported_deformation hDcv hfzero
  let ε := min (r / 2) (min (η / 2) (ε₀ / 4))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεr : ε ≤ r / 2 := min_le_left _ _
  have hεη : ε ≤ η / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεsmall : ε ≤ ε₀ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, hε, by linarith, ?_⟩
  intro a b ha hb hab hcap
  let δ := b - a
  have hδ : 0 ≤ δ := sub_nonneg.mpr hab
  have hδsmall : |δ| ≤ ε₀ := by
    rw [abs_of_nonneg hδ]
    have ha' := (abs_le.mp ha).1
    have hb' := (abs_le.mp hb).2
    dsimp [δ]
    linarith
  have haI : a ∈ Icc (-r) r := by
    obtain ⟨hal, hau⟩ := abs_le.mp ha
    constructor <;> linarith
  have hbI : b ∈ Icc (-r) r := by
    obtain ⟨hbl, hbu⟩ := abs_le.mp hb
    constructor <;> linarith
  obtain ⟨T, hT, hTfix, _, tD, htD, htDval⟩ := hsmall δ hδsmall
  have hTformula (p : E × ℝ) : T p = (p.1, p.2 + δ * σ p) := by
    by_cases hp : p ∈ D
    · rw [hT p hp]
      apply Prod.ext
      · change p.1 + δ • (0 : E) = p.1
        simp
      · rfl
    · have hpL : p ∉ L.space := fun h => hp (interior_subset (hUinside (hLU h)))
      rw [hTfix p (fun hi => hp (interior_subset hi)), hσoff p hpL]
      simp
  have hTfirst (p : E × ℝ) : (T p).1 = p.1 := by rw [hTformula]
  have htDfirst (p : D) : (tD p : E × ℝ).1 = (p : E × ℝ).1 :=
    (congrArg Prod.fst (htDval p)).trans (hTfirst p)
  have hToff (p : E × ℝ) (hp : p ∉ L.space) : T p = p := by
    rw [hTformula, hσoff p hp]
    simp
  have hTunit (x : E) (hx : x ∈ d) : T (x, a) = (x, b) := by
    have haη : a ∈ Icc (-η / 2) (η / 2) := by
      obtain ⟨hal, hau⟩ := abs_le.mp (ha.trans hεη)
      constructor <;> linarith
    have hσone : σ (x, a) = 1 := congrArg Prod.fst (hgunit ⟨hx, haη⟩)
    rw [hTformula, hσone]
    congr 1
    dsimp [δ]
    ring
  have hTmono (x : E) :
      StrictMonoOn (fun t : ℝ => (T (x, t)).2) (Icc (-r) r) := by
    have hcont : Continuous (fun t : ℝ => (T (x, t)).2) :=
      continuous_snd.comp (T.continuous.comp (continuous_const.prodMk continuous_id))
    have hinj : Function.Injective (fun t : ℝ => (T (x, t)).2) := by
      intro t s hts
      have heq : T (x, t) = T (x, s) :=
        Prod.ext ((hTfirst (x, t)).trans (hTfirst (x, s)).symm) hts
      exact congrArg Prod.snd (T.injective heq)
    have hlo : T (x, -r) = (x, -r) := by
      apply hTfix
      intro hp
      rw [show D = K.space ×ˢ Icc (-r) r from rfl,
        interior_prod_eq, interior_Icc] at hp
      exact (lt_irrefl (-r)) hp.2.1
    have hhi : T (x, r) = (x, r) := by
      apply hTfix
      intro hp
      rw [show D = K.space ×ˢ Icc (-r) r from rfl,
        interior_prod_eq, interior_Icc] at hp
      exact (lt_irrefl r) hp.2.2
    apply hcont.continuousOn.strictMonoOn_of_injOn_Icc (by linarith) _ hinj.injOn
    rw [hlo, hhi]
    exact neg_le_self hr.le
  have hTcut (p : D) (hpq : (p : E × ℝ).1 ∈ q) :
      (tD p : E × ℝ).2 ≤ b ↔ (p : E × ℝ).2 ≤ a := by
    have hmono := hTmono (p : E × ℝ).1
    have haeq := congrArg Prod.snd (hTunit _ (hqd hpq))
    rw [htDval]
    constructor
    · intro hp
      by_contra hn
      have hlt := hmono haI p.property.2 (lt_of_not_ge hn)
      change (T ((p : E × ℝ).1, a)).2 <
        (T ((p : E × ℝ).1, (p : E × ℝ).2)).2 at hlt
      rw [haeq] at hlt
      exact (not_le_of_gt hlt) hp
    · intro hp
      exact (hmono.monotoneOn p.property.2 haI hp).trans_eq haeq
  let gD : D ≃ₜ D := e.symm.trans (tD.trans e)
  have hgD : gD.IsFinitePL := he.symm.trans (htD.trans he)
  have hgDfront (p : D) (hp : (p : E × ℝ) ∈ frontier D) : gD p = p := by
    have hn : (e.symm p : E × ℝ) ∉ interior D := by
      intro hi
      have hei := he.mem_interior rfl hi
      rw [e.apply_symm_apply] at hei
      exact hp.2 hei
    have htfix : tD (e.symm p) = e.symm p :=
      Subtype.ext ((htDval _).trans (hTfix _ hn))
    change e (tD (e.symm p)) = p
    rw [htfix, e.apply_symm_apply]
  let G : (E × ℝ) ≃ₜ (E × ℝ) := gD.closedExtension hDcompact.isClosed hgDfront
  have hGmem (p : E × ℝ) (hp : p ∈ D) : G p = (gD ⟨p, hp⟩ : E × ℝ) :=
    gD.closedExtension_apply_mem hDcompact.isClosed hgDfront hp
  have hGoff (p : E × ℝ) (hp : p ∉ D) : G p = p :=
    gD.closedExtension_apply_notMem hDcompact.isClosed hgDfront hp
  have hGe (p : D) : G (e p : E × ℝ) = (e (tD p) : E × ℝ) := by
    rw [hGmem _ (e p).property]
    change (e (tD (e.symm (e p))) : E × ℝ) = _
    rw [e.symm_apply_apply]
  have hGfinite : ∀ J : SimplicialComplex ℝ (E × ℝ), J.faces.Finite →
      FinitePiecewiseAffineOn (G : E × ℝ → E × ℝ) J.space := by
    obtain ⟨fG, hfG, hfg⟩ := hgD
    have hGD : FinitePiecewiseAffineOn (G : E × ℝ → E × ℝ) D :=
      hfG.congr (fun p hp => (hfg ⟨p, hp⟩).symm.trans (hGmem p hp).symm)
    exact hGD.homeomorph_on_finite_polyhedron_of_eq_id_off hGoff
  have hGfix (z : E × ℝ) (hz : z ∉ interior C) : G z = z := by
    by_cases hzD : z ∈ D
    · let p : D := e.symm ⟨z, hzD⟩
      have hep : (e p : E × ℝ) = z := congrArg Subtype.val (e.apply_symm_apply ⟨z, hzD⟩)
      have hpL : (p : E × ℝ) ∉ L.space := by
        intro hp
        have h := (hLU hp).2
        change H (p : E × ℝ) ∈ interior C at h
        rw [hHe p, hep] at h
        exact hz h
      have htfix : tD p = p := Subtype.ext ((htDval p).trans (hToff p hpL))
      rw [← hep, hGe, htfix]
    · exact hGoff z hzD
  have hGC : G '' C = C := G.image_eq_self_of_eqOn_compl
    (fun z hz => hGfix z (fun hi => hz (interior_subset hi)))
  have hGinterior : G '' interior C = interior C :=
    (G.image_interior C).trans (congrArg interior hGC)
  have hGsublevel : G '' (S ∩ {p | p.2 ≤ a}) = S ∩ {p | p.2 ≤ b} := by
    apply Subset.antisymm
    · rintro z ⟨x, ⟨hxS, hxa⟩, rfl⟩
      by_cases hxD : x ∈ D
      · let p : D := e.symm ⟨x, hxD⟩
        have hep : (e p : E × ℝ) = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hxD⟩)
        have hpq : (p : E × ℝ).1 ∈ q := (hsection p).mp (hep.symm ▸ hxS)
        rw [← hep, hGe]
        refine ⟨(hsection (tD p)).mpr ((htDfirst p).symm ▸ hpq), ?_⟩
        change (e (tD p) : E × ℝ).2 ≤ b
        rw [hheight]
        apply (hTcut p hpq).mpr
        have hpheight : (p : E × ℝ).2 = x.2 := (hheight p).symm.trans (congrArg Prod.snd hep)
        rwa [hpheight]
      · rw [hGoff x hxD]
        exact ⟨hxS, hxa.trans hab⟩
    · intro z hz
      by_cases hzD : z ∈ D
      · let p : D := e.symm ⟨z, hzD⟩
        let w : D := tD.symm p
        have hep : (e p : E × ℝ) = z := congrArg Subtype.val (e.apply_symm_apply ⟨z, hzD⟩)
        have htw : tD w = p := tD.apply_symm_apply p
        have hpq : (p : E × ℝ).1 ∈ q := (hsection p).mp (hep.symm ▸ hz.1)
        have hwq : (w : E × ℝ).1 ∈ q := by
          have h := htDfirst w
          rw [htw] at h
          exact h ▸ hpq
        refine ⟨e w, ⟨(hsection w).mpr hwq, ?_⟩, ?_⟩
        · change (e w : E × ℝ).2 ≤ a
          rw [hheight]
          apply (hTcut w hwq).mp
          rw [htw, ← hheight p, hep]
          exact hz.2
        · rw [hGe, htw, hep]
      · have hza : z.2 ≤ a := by
          by_contra hn
          have hzI : z.2 ∈ Icc (-r) r :=
            ⟨haI.1.trans (le_of_lt (lt_of_not_ge hn)), hz.2.trans hbI.2⟩
          exact hzD (hband ⟨hz.1, hzI⟩)
        exact ⟨z, ⟨hz.1, hza⟩, hGoff z hzD⟩
  have hGdisk : G '' cylinderSlice e d a = cylinderSlice e d b := by
    apply Subset.antisymm
    · rintro z ⟨x, ⟨p, hpd, hpa, rfl⟩, rfl⟩
      refine ⟨tD p, (htDfirst p).symm ▸ hpd, ?_, (hGe p).symm⟩
      rw [htDval]
      have heq : (p : E × ℝ) = ((p : E × ℝ).1, a) := Prod.ext rfl hpa
      rw [heq, hTunit _ hpd]
    · rintro z ⟨p, hpd, hpb, rfl⟩
      let p₀ : D := ⟨((p : E × ℝ).1, a), p.property.1, haI⟩
      have htp : tD p₀ = p := by
        apply Subtype.ext
        rw [htDval, hTunit _ hpd]
        exact Prod.ext rfl hpb.symm
      refine ⟨e p₀, ⟨p₀, hpd, rfl, rfl⟩, ?_⟩
      rw [hGe, htp]
  have hGbelow : G '' {p : E × ℝ | p.2 ≤ a} ⊆ {p | p.2 ≤ b} := by
    rintro z ⟨x, hxa, rfl⟩
    change x.2 ≤ a at hxa
    by_cases hxD : x ∈ D
    · let p : D := e.symm ⟨x, hxD⟩
      have hep : (e p : E × ℝ) = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hxD⟩)
      change (G x).2 ≤ b
      rw [← hep, hGe, hheight, htDval, hTformula]
      have hpheight : (p : E × ℝ).2 = x.2 :=
        (hheight p).symm.trans (congrArg Prod.snd hep)
      have hσle : σ p ≤ 1 := (hgbound p).2
      have hmul := mul_le_mul_of_nonneg_left hσle hδ
      dsimp [δ] at hmul ⊢
      rw [hpheight]
      nlinarith
    · rw [hGoff x hxD]
      exact hxa.trans hab
  obtain ⟨B, hB, hBC, hBbelow, hBE⟩ := hcap
  have hboundary :
      G '' (cylinderSlice e d a ∪ (S ∩ {p | p.2 ≤ a})) =
        cylinderSlice e d b ∪ (S ∩ {p | p.2 ≤ b}) := by
    rw [image_union, hGdisk, hGsublevel]
  have hB' := hB.image_of_finitePL_on_finite_polyhedra G hGfinite
  rw [hboundary] at hB'
  have hBE' := G.isFinitePLBallPair_cylinderComplement_image_iff
    (V := (ℝ × ℝ) × ℝ) hGfinite hGC (Icc (-1 : ℝ) 1) (1 : ℝ)
      (interior B) (cylinderSlice e d a ∪ (S ∩ {p | p.2 ≤ a}))
  simp only [← Set.prod_singleton, G.image_interior, hboundary] at hBE'
  refine ⟨G '' B, hB', (image_mono hBC).trans hGinterior.subset,
    (image_mono hBbelow).trans hGbelow, hBE'.mpr hBE⟩




theorem HasPairedHeightCap.regionBalls_of_terminal
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {S C d T : Set F} {A : F → ℝ} {c : ℝ}
    (hcap : HasPairedHeightCap S C d A c)
    (hdim : Module.finrank ℝ F = 3)
    (hT : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) T (d ∪ (S ∩ {x | c ≤ A x})))
    (hTE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior T ×ˢ {1})
      ((d ∪ (S ∩ {x | c ≤ A x})) ×ˢ {(1 : ℝ)}))
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (S ∩ {x | A x = c}))
    (hdplane : d ⊆ {x | A x = c}) (hdcontact : d ∩ S = S ∩ {x | A x = c})
    (hTabove : T ⊆ {x | c ≤ A x}) (hTcut : T ∩ {x | A x = c} = d)
    (hlower : (S ∩ {x | A x < c}).Nonempty)
    (hupper : (S ∩ {x | c < A x}).Nonempty) (hTC : T ⊆ interior C)
    (K : SimplicialComplex ℝ F) (hK : K.faces.Finite)
    (hC : IsCompact C) (hCcv : Convex ℝ C) (hCne : (interior C).Nonempty)
    (hKC : K.space = C) : Set.HasAlexanderRegionBalls S C := by
  obtain ⟨B, hB, hBC, hBbelow, hBE⟩ := hcap
  exact Set.HasAlexanderRegionBalls.of_height_cut_contact A hdim hB hT hBE hTE hd
    hdplane hdcontact hBbelow hTabove hTcut hlower hupper hBC hTC K hK hC hCcv hCne hKC

end PoincareConjecture.M76.ZeroChargeJoint
