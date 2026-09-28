import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.OrdinaryArcParameters
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCircleArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]


theorem finitePLInterval_exists_fixedPoint {U : Set E} {a b : E}
    (hU : IsFinitePLBallPair ℝ U {a, b}) (hab : a ≠ b)
    {p : E → E} (hp : ContinuousOn p U) (hpU : MapsTo p U U) :
    ∃ x ∈ U, p x = x := by
  classical
  obtain ⟨alpha, _, _, _⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  let q : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
    fun t => alpha.symm ⟨p (alpha t), hpU (alpha t).property⟩
  have hq : Continuous q := alpha.symm.continuous.comp
    ((hp.comp_continuous (continuous_subtype_val.comp alpha.continuous)
      fun t => (alpha t).property).subtype_mk _)
  let Q : ℝ → ℝ := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then q ⟨t, ht⟩ else 0
  have hQval (t : Icc (0 : ℝ) 1) : Q t = q t := by
    dsimp only [Q]
    rw [dif_pos t.property]
  have hQ : ContinuousOn Q (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp hq using 1
    ext t
    exact hQval t
  have hQI : MapsTo Q (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    rw [hQval ⟨t, ht⟩]
    exact (q ⟨t, ht⟩).property
  obtain ⟨t, ht, hfix⟩ := exists_mem_Icc_isFixedPt_of_mapsTo hQ zero_le_one hQI
  have hqt : q ⟨t, ht⟩ = ⟨t, ht⟩ := Subtype.ext ((hQval ⟨t, ht⟩).symm.trans hfix)
  refine ⟨alpha ⟨t, ht⟩, (alpha ⟨t, ht⟩).property, ?_⟩
  have h := congrArg (fun z => (alpha z : E)) hqt
  change (alpha (alpha.symm _) : E) = _ at h
  simpa only [alpha.apply_symm_apply] using h



theorem freeInvolution_exchanges_circle_arcs
    {U V : Set E} {a b : E} (hU : IsFinitePLBallPair ℝ U {a, b})
    (hV : IsFinitePLBallPair ℝ V {a, b}) (hab : a ≠ b)
    (hinter : U ∩ V = {a, b}) {p : E → E}
    (hp : ContinuousOn p (U ∪ V)) (hpUV : MapsTo p (U ∪ V) (U ∪ V))
    (hinv : ∀ x ∈ U ∪ V, p (p x) = x)
    (hfree : ∀ x ∈ U ∪ V, p x ≠ x) (hpa : p a = b) (hpb : p b = a) :
    p '' U = V ∧ p '' V = U := by
  have hside {S T : Set E} (hS : IsFinitePLBallPair ℝ S {a, b})
      (hT : IsFinitePLBallPair ℝ T {a, b}) (hST : S ∪ T = U ∪ V)
      (hinterST : S ∩ T = {a, b}) : MapsTo p S T := by
    have hSc : S ⊆ U ∪ V := subset_union_left.trans hST.subset
    have havoid : Disjoint (p '' (S \ {a, b})) ({a, b} : Set E) := by
      rw [disjoint_left]
      rintro y ⟨x, hx, rfl⟩ (ha | hb)
      · have heq : x = b := (hinv x (hSc hx.1)).symm.trans ((congrArg p ha).trans hpa)
        exact hx.2 (Or.inr heq)
      · have heq : x = a := (hinv x (hSc hx.1)).symm.trans ((congrArg p hb).trans hpb)
        exact hx.2 (Or.inl heq)
    have hconn := hS.isConnected_sdiff.image p (hp.mono (sdiff_subset.trans hSc))
    have hcover : p '' (S \ {a, b}) ⊆ S ∪ T := by
      rintro _ ⟨x, hx, rfl⟩
      exact hST.symm.subset (hpUV (hSc hx.1))
    have hchoose : p '' (S \ {a, b}) ⊆ S ∨ p '' (S \ {a, b}) ⊆ T := by
      by_cases hs : p '' (S \ {a, b}) ⊆ S
      · exact Or.inl hs
      · right
        obtain ⟨x, hx, hxs⟩ := not_subset.mp hs
        intro y hy
        by_contra hyt
        obtain ⟨z, hz, hzST⟩ := isPreconnected_closed_iff.mp hconn.isPreconnected S T
          hS.isCompact.isClosed hT.isCompact.isClosed hcover
          ⟨y, hy, (hcover hy).resolve_right hyt⟩ ⟨x, hx, (hcover hx).resolve_left hxs⟩
        exact disjoint_left.mp havoid hz (hinterST.subset hzST)
    have hext {Z : Set E} (hZ : IsFinitePLBallPair ℝ Z {a, b})
        (hsub : p '' (S \ {a, b}) ⊆ Z) : MapsTo p S Z := by
      intro x hx
      by_cases hm : x ∈ ({a, b} : Set E)
      · rcases hm with rfl | rfl
        · exact hpa ▸ hZ.1 (Or.inr rfl)
        · exact hpb ▸ hZ.1 (Or.inl rfl)
      · exact hsub ⟨x, ⟨hx, hm⟩, rfl⟩
    rcases hchoose with hsame | hother
    · obtain ⟨x, hx, hfix⟩ := finitePLInterval_exists_fixedPoint hS hab
        (hp.mono hSc) (hext hS hsame)
      exact (hfree x (hSc hx) hfix).elim
    · exact hext hT hother
  have hUV := hside hU hV rfl hinter
  have hVU := hside hV hU (union_comm V U) ((inter_comm V U).trans hinter)
  constructor
  · apply Subset.antisymm (image_subset_iff.mpr hUV)
    intro x hx
    exact ⟨p x, hVU hx, hinv x (Or.inr hx)⟩
  · apply Subset.antisymm (image_subset_iff.mpr hVU)
    intro x hx
    exact ⟨p x, hUV hx, hinv x (Or.inl hx)⟩

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}




theorem OrdinaryDoubleCurveModel.exists_selfpaired_twofold_source_arcs
    [T2Space X] (M : OrdinaryDoubleCurveModel e f R)
    (hf : PolyhedralPLInCharts e f D2) (hinside : MapsTo f D2 R)
    (hfrontier : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (i : M.Index) (hself : M.mate i = i) :
    ∃ (a b : V2) (U V : Set V2) (alpha : I01 ≃ₜ U) (beta : I01 ≃ₜ V),
      a ≠ b ∧ IsFinitePLBallPair ℝ U {a, b} ∧ IsFinitePLBallPair ℝ V {a, b} ∧
      U ∪ V = M.pieces i ∧ U ∩ V = {a, b} ∧
      alpha.IsFinitePL ∧ beta.IsFinitePL ∧
      (alpha 0 : V2) = a ∧ (alpha 1 : V2) = b ∧
      (beta 0 : V2) = b ∧ (beta 1 : V2) = a ∧
      (∀ u : I01, ∃ hx : (alpha u : V2) ∈ doubleLocusOn f D2,
        (beta u : V2) = (M.partner ⟨alpha u, hx⟩ : V2)) ∧
      (∀ u : I01, f (alpha u) = f (beta u)) ∧
      (∀ u v : I01, f (alpha u) = f (alpha v) ↔
        u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)) ∧
      f '' U = f '' M.pieces i ∧ f '' V = f '' M.pieces i := by
  classical
  obtain ⟨n, P, hPi, hP, hPs, _⟩ : ∃ (n : ℕ) (P : Polygon V2 (n + 3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧ P.boundary ℝ = M.pieces i ∧
      Disjoint (M.pieces i) Q2 := by
    rcases M.models i with hball | hcircle
    · exact ((M.exists_interval_arc_parameters hf hinside hfrontier i hball).1 hself).elim
    · exact hcircle
  obtain ⟨p, hp, hpval⟩ := M.partnerPL
  have hsub := M.piece_subset_double i
  have hpval' (x : V2) (hx : x ∈ doubleLocusOn f D2) :
      p x = (M.partner ⟨x, hx⟩ : V2) := (hpval ⟨x, hx⟩).symm
  have hpM : MapsTo p (M.pieces i) (M.pieces i) := by
    intro x hx
    rw [hpval' x (hsub hx)]
    simpa only [hself] using M.partner_component i ⟨x, hsub hx⟩ hx
  have hinv (x : V2) (hx : x ∈ M.pieces i) : p (p x) = x := by
    calc
      p (p x) = p (M.partner ⟨x, hsub hx⟩) := congrArg p (hpval' x (hsub hx))
      _ = (M.partner (M.partner ⟨x, hsub hx⟩) : V2) := (hpval _).symm
      _ = x := congrArg Subtype.val (M.partner_involutive ⟨x, hsub hx⟩)
  have hfree (x : V2) (hx : x ∈ M.pieces i) : p x ≠ x := by
    rw [hpval' x (hsub hx)]
    exact M.partner_free ⟨x, hsub hx⟩
  obtain ⟨a, ha⟩ := (M.connected i).nonempty
  let b := p a
  have hb : b ∈ M.pieces i := hpM ha
  have hab : a ≠ b := (hfree a ha).symm
  obtain ⟨U, V, hU, hV, hUV, hinter⟩ := P.exists_arcs_at_marks hP hPi
    (hPs.symm ▸ ha) (hPs.symm ▸ hb) hab
  have hcover : U ∪ V = M.pieces i := hUV.trans hPs
  have hUG : U ⊆ doubleLocusOn f D2 := subset_union_left.trans (hcover.subset.trans hsub)
  have hVG : V ⊆ doubleLocusOn f D2 := subset_union_right.trans (hcover.subset.trans hsub)
  have hswap : p '' U = V ∧ p '' V = U := freeInvolution_exchanges_circle_arcs
    hU hV hab hinter (hp.continuousOn.mono (hcover.subset.trans hsub))
    (by simpa only [hcover] using hpM) (by simpa only [hcover] using hinv)
    (by simpa only [hcover] using hfree) rfl (hinv a ha)
  have hmem (x : doubleLocusOn f D2) :
      (x : V2) ∈ U ↔ (M.partner x : V2) ∈ V := by
    rw [← hpval' x x.property]
    constructor
    · intro hx
      exact hswap.1.subset ⟨x, hx, rfl⟩
    · intro hx
      have hpx := hswap.2.subset (mem_image_of_mem p hx)
      have hxx : p (p x) = (x : V2) := by
        calc
          p (p x) = p (M.partner x) := congrArg p (hpval x).symm
          _ = (M.partner (M.partner x) : V2) := (hpval _).symm
          _ = x := congrArg Subtype.val (M.partner_involutive x)
      exact hxx ▸ hpx
  let d := M.partner.restrictSubsets hUG hVG hmem
  have htri := hU
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := htri
  have hd : d.IsFinitePL := M.partnerPL.restrictSubsets hUG hVG hmem K hK hKs
  obtain ⟨alpha, halpha, ha0, ha1⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  change (alpha (0 : I01) : V2) = a at ha0
  change (alpha (1 : I01) : V2) = b at ha1
  let beta := alpha.trans d
  have hbeta : beta.IsFinitePL := halpha.trans hd
  have hbetaval (u : I01) : (beta u : V2) = p (alpha u) :=
    (hpval' (alpha u) (hUG (alpha u).property)).symm
  have hb0 : (beta 0 : V2) = b := by rw [hbetaval, ha0]
  have hb1 : (beta 1 : V2) = a := by rw [hbetaval, ha1]; exact hinv a ha
  have hsync (u : I01) : f (alpha u) = f (beta u) :=
    (M.partner_value ⟨alpha u, hUG (alpha u).property⟩).symm
  have hend : f (alpha (0 : I01)) = f (alpha (1 : I01)) := by
    rw [hsync, hb0, ha1]
  have hfib (u v : I01) : f (alpha u) = f (alpha v) ↔
      u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
    constructor
    · intro huv
      by_cases heq : (alpha u : V2) = (alpha v : V2)
      · exact Or.inl (alpha.injective (Subtype.ext heq))
      · have hvp := M.unique_partner ⟨alpha u, hUG (alpha u).property⟩ (alpha v)
          (hUG (alpha v).property).1 huv heq
        have hvV : (alpha v : V2) ∈ V := hvp ▸ (hmem ⟨alpha u,
          hUG (alpha u).property⟩).mp (alpha u).property
        rcases hinter.subset ⟨(alpha v).property, hvV⟩ with hv0 | hv1
        · have hv : v = 0 := alpha.injective (Subtype.ext (hv0.trans ha0.symm))
          have hu : u = 1 := by
            have h := congrArg p hvp
            rw [← hpval' (alpha u) (hUG (alpha u).property),
              hinv _ (hcover.subset (Or.inl (alpha u).property)), hv0] at h
            exact alpha.injective (Subtype.ext (h.symm.trans ha1.symm))
          exact Or.inr (Or.inr ⟨hu, hv⟩)
        · have hv : v = 1 := alpha.injective (Subtype.ext (hv1.trans ha1.symm))
          have hu : u = 0 := by
            have h := congrArg p hvp
            rw [← hpval' (alpha u) (hUG (alpha u).property),
              hinv _ (hcover.subset (Or.inl (alpha u).property)), hv1] at h
            have h' : a = (alpha u : V2) := (hinv a ha).symm.trans h
            exact alpha.injective (Subtype.ext (h'.symm.trans ha0.symm))
          exact Or.inr (Or.inl ⟨hu, hv⟩)
    · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rfl
      · exact hend
      · exact hend.symm
  have hphysical : f '' U = f '' V := by
    rw [← hswap.1, image_image]
    apply image_congr
    intro x hx
    rw [hpval' x (hUG hx)]
    exact (M.partner_value ⟨x, hUG hx⟩).symm
  refine ⟨a, b, U, V, alpha, beta, hab, hU, hV, hcover, hinter, halpha, hbeta,
    ha0, ha1, hb0, hb1, fun u => ⟨hUG (alpha u).property, rfl⟩, hsync, hfib, ?_, ?_⟩
  · rw [← hcover, image_union, ← hphysical, union_self]
  · rw [← hcover, image_union, hphysical, union_self]

end PoincareConjecture.M76.Dehn
