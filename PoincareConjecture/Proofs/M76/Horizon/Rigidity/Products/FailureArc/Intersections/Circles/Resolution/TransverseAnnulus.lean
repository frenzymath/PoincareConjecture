import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.TransverseStrip

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_transverse_cap_annulus
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {L d ε : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hε : 0 ≤ ε) (hεd : ε < 2 * d)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (_root_.Dehn.identityTube L d))
    (hfib : ∀ z ∈ _root_.Dehn.identityTube L d, ∀ w ∈ _root_.Dehn.identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) :
    ∃ g : P2 → X,
      Topology.IsEmbedding (fun x : squareAnnulus L d ↦ g x) ∧
      PolyhedralPLInCharts e g (squareAnnulus L d) ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), u)) =
          τ (capStrip d ε (s, u))) ∧
      g '' squareAnnulus L d = τ '' (capStrip d ε '' rectangle (4 * L) d) ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)),
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), -d)) = τ ((-d, d), s) ∧
        g (annulusMap L (by linarith) ((s : AddCircle (4 * L)), d)) = τ ((d - ε, d), s)) := by
  classical
  have hL : 0 < L := by linarith
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  have hmap := capStrip_mapsTo (L := L) hd hε hεd
  have hstrip := capStrip_finitePL hd hL ε
  have hstripcopy := hstrip
  obtain ⟨K, hK, hKs, _⟩ := hstripcopy
  have hφ : PolyhedralPLInCharts e (τ ∘ capStrip d ε) (rectangle (4 * L) d) := by
    have hh := hτ.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hstrip)
      (fun _ hx ↦ hmap (hKs.subset hx))
    exact hKs ▸ hh
  have hend (u : Icc (-d) d) :
      τ (capStrip d ε (0, u)) = τ (capStrip d ε (4 * L, u)) := by
    apply (hfib _ (hmap ⟨⟨le_rfl, by positivity⟩, u.property⟩)
      _ (hmap ⟨⟨by positivity, le_rfl⟩, u.property⟩)).mpr
    exact ⟨rfl, by simp only [capStrip, AddCircle.coe_zero, AddCircle.coe_period]⟩
  let a : AddCircle (4 * L) × Icc (-d) d → X := fun p ↦
    AddCircle.liftIco (4 * L) 0 (fun s ↦ τ (capStrip d ε (s, p.2))) p.1
  have ha (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d) :
      a ((s : AddCircle (4 * L)), u) = τ (capStrip d ε (s, u)) :=
    AddCircle.liftIco_zero_coe_apply_Icc (hend u) hs
  have hac : Continuous a := by
    apply AddCircle.continuous_parametric_liftIco
      (fun p : ℝ × Icc (-d) d ↦ τ (capStrip d ε (p.1, p.2)))
    exacts [hφ.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)) (fun p ↦ ⟨p.1.property, p.2.property⟩), hend]
  have hrep (z : AddCircle (4 * L)) :
      ∃ s ∈ Icc 0 (4 * L), (s : AddCircle (4 * L)) = z :=
    ⟨AddCircle.equivIco (4 * L) 0 z,
      ⟨(AddCircle.equivIco (4 * L) 0 z).property.1,
        by simpa only [zero_add] using (AddCircle.equivIco (4 * L) 0 z).property.2.le⟩,
      AddCircle.coe_equivIco⟩
  have hai : Function.Injective a := by
    rintro ⟨z, u⟩ ⟨w, v⟩ heq
    obtain ⟨s, hs, rfl⟩ := hrep z
    obtain ⟨t, ht, rfl⟩ := hrep w
    rw [ha s hs u, ha t ht v] at heq
    have hh := (hfib _ (hmap ⟨hs, u.property⟩) _ (hmap ⟨ht, v.property⟩)).mp heq
    exact Prod.ext hh.2 (Subtype.ext (capStrip_transverse_injective hd hεd hh.1))
  obtain ⟨E, g, hE, hg, hgE, hgperiod, hgemb⟩ :=
    _root_.Dehn.exists_square_annulus_map_of_period hcompat hd hwidth (τ ∘ capStrip d ε) hφ a ha
  have himage : g '' squareAnnulus L d = τ '' (capStrip d ε '' rectangle (4 * L) d) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      let p := E.symm ⟨x, hx⟩
      obtain ⟨s, hs, hz⟩ := hrep p.1
      have hp : E p = ⟨x, hx⟩ := E.apply_symm_apply _
      refine ⟨capStrip d ε (s, p.2), ⟨(s, p.2), ⟨hs, p.2.property⟩, rfl⟩, ?_⟩
      have hv := hgE p
      rw [hp] at hv
      rw [hv]
      exact (ha s hs p.2).symm.trans (congrArg a (Prod.ext hz rfl))
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      let q : AddCircle (4 * L) × Icc (-d) d := ((p.1 : AddCircle (4 * L)), ⟨p.2, hp.2⟩)
      exact ⟨E q, (E q).property, (hgE q).trans (ha p.1 hp.1 q.2)⟩
  refine ⟨g, hgemb (hac.isClosedEmbedding hai).isEmbedding, hg, hgperiod, himage, ?_⟩
  intro s hs
  have hm := hgperiod s hs ⟨-d, ⟨le_rfl, by linarith⟩⟩
  have hp := hgperiod s hs ⟨d, ⟨by linarith, le_rfl⟩⟩
  simpa only [Function.comp_apply, capStrip_outer d ε s hd.ne', capStrip_inner d ε s hd.ne']
    using And.intro hm hp

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
