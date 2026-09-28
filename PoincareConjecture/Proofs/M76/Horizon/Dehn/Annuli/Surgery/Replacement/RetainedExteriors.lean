import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.ThreeCylinderMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.SquareCylinder
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.TubeAnnulus










set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => (Set.prod Q (Icc (-1 : ℝ) 1) : Set (V2 × ℝ))
local notation "Left" => (Set.prod Q (Icc (-1 : ℝ) (-(1 / 2 : ℝ))) : Set (V2 × ℝ))
local notation "Middle" => (Set.prod Q (Icc (-(1 / 2 : ℝ)) 0) : Set (V2 × ℝ))
local notation "Right" => (Set.prod Q (Icc (0 : ℝ) 1) : Set (V2 × ℝ))

private theorem exists_cylinder_map_pullback
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X F}
    {T U : Set E} (H : Cyl ≃ₜ T) (hH : H.IsFinitePL) (hTU : T ⊆ U)
    (f : E → X) (hf : PolyhedralPLInCharts e f U) :
    ∃ k : (V2 × ℝ) → X, PolyhedralPLInCharts e k Cyl ∧
      (∀ x : Cyl, k x = f (H x)) ∧ k '' Cyl = f '' T := by
  obtain ⟨p, hp, hpv⟩ := hH
  have hpcopy := hp
  obtain ⟨K, hK, hKs, _⟩ := hpcopy
  have hmap : MapsTo p Cyl U := by
    intro x hx
    rw [← hpv ⟨x, hx⟩]
    exact hTU (H ⟨x, hx⟩).property
  refine ⟨f ∘ p, ?_, fun x ↦ congrArg f (hpv x).symm, ?_⟩
  · have hh := hf.comp_finitePiecewiseAffineOn K hK
      (by simpa only [hKs] using hp) (fun _ hx ↦ hmap (hKs.subset hx))
    simpa only [hKs] using hh
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨H ⟨x, hx⟩, (H ⟨x, hx⟩).property, congrArg f (hpv ⟨x, hx⟩)⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨H.symm ⟨x, hx⟩, (H.symm ⟨x, hx⟩).property, ?_⟩
      change f (p (H.symm ⟨x, hx⟩)) = f x
      rw [← hpv, H.apply_symm_apply]

theorem exists_resolving_annulus_with_retained_exteriors_and_levels
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (hb : 0 < b) (hbd : b < d)
    (A : Fin 2 → Set E) (c : ∀ k, squareAnnulus L d ≃ₜ A k)
    (hc : ∀ k, (c k).IsFinitePL) (j : Fin 2)
    {O I U : Set E} (outer : Cyl ≃ₜ O) (inner : Cyl ≃ₜ I)
    (houter : outer.IsFinitePL) (hinner : inner.IsFinitePL)
    (hOU : O ⊆ U) (hIU : I ⊆ U)
    (hOA : ∀ x : Cyl, (outer x : E) ∈ A j ↔ x.val.2 = 1)
    (hAO : ∀ p : squareAnnulus L d, (c j p : E) ∈ O ↔ depth L p = -d)
    (hAI : ∀ p : squareAnnulus L d, (c j.rev p : E) ∈ I ↔ depth L p = d)
    (hIA : ∀ x : Cyl, (inner x : E) ∈ A j.rev ↔ x.val.2 = -1)
    (f : E → X) (hf : PolyhedralPLInCharts e f U) (τ : (P2 × ℝ) → X)
    (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hvalue : ∀ (k : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L))
      (u : Icc (-d) d),
      f (c k ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) = τ (sourceTubeDiagonal k u, s)) :
    ∃ (a : P2 → X) (g : (V2 × ℝ) → X)
      (copyO : O ≃ₜ Left) (copyA : squareAnnulus L d ≃ₜ Middle)
      (copyI : I ≃ₜ Right) (q : Q ≃ₜ Q),
      Topology.IsEmbedding (fun p : squareAnnulus L d ↦ a p) ∧
      PolyhedralPLInCharts e a (squareAnnulus L d) ∧
      a '' squareAnnulus L d ⊆ τ '' identityTube L d ∧
      PolyhedralPLInCharts e g Cyl ∧
      copyO.IsFinitePL ∧ copyA.IsFinitePL ∧ copyI.IsFinitePL ∧ q.IsFinitePL ∧
      (∀ x : O, g (copyO x) = f x) ∧
      (∀ x : squareAnnulus L d, g (copyA x) = a x) ∧
      (∀ x : I, g (copyI x) = f x) ∧
      (∀ u : Q, g (u, -1) =
        f (outer ⟨(u, -1), u.property, le_rfl, by norm_num⟩)) ∧
      (∀ u : Q, g (u, 1) =
        f (inner ⟨(q u, 1), (q u).property, by norm_num, le_rfl⟩)) ∧
      g '' Cyl = (f '' O ∪ a '' squareAnnulus L d) ∪ f '' I ∧
      (∀ x : O, (copyO x).val.2 = ((outer.symm x).val.2 - 3) / 4) ∧
      (∀ x : squareAnnulus L d,
        (copyA x).val.2 = -(1 / 2 : ℝ) ↔ depth L x = -d) ∧
      (∀ x : squareAnnulus L d, (copyA x).val.2 = 0 ↔ depth L x = d) ∧
      (∀ x : I, (copyI x).val.2 = ((inner.symm x).val.2 + 1) / 2) := by
  obtain ⟨a, haemb, ha, hasub, _, ha0, ha1⟩ :=
    exists_resolving_annulus_retained_seams e hcompat hd hwidth hb hbd A c f τ hτ hfib hvalue j
  obtain ⟨H, hH, hH0, hH1⟩ := exists_square_annulus_cylinder_chart (L := L) hd (by linarith)
  let collar₀ := H.trans (c j)
  let collar₁ := H.trans (c j.rev)
  have hcollar₀ : collar₀.IsFinitePL := hH.trans (hc j)
  have hcollar₁ : collar₁.IsFinitePL := hH.trans (hc j.rev)
  have hcontact₀ (x : Cyl) : (collar₀ x : E) ∈ O ↔ x.val.2 = -1 :=
    (hAO (H x)).trans (hH0 x).symm
  have hcontact₁ (x : Cyl) : (collar₁ x : E) ∈ I ↔ x.val.2 = 1 :=
    (hAI (H x)).trans (hH1 x).symm
  obtain ⟨q₀, hq₀, hq₀v⟩ := exists_cylinder_end_comparison
    outer collar₀ houter hcollar₀ hOA hcontact₀
  obtain ⟨q₁, hq₁, hq₁v⟩ := exists_cylinder_end_comparison
    collar₁ inner hcollar₁ hinner hcontact₁ hIA
  obtain ⟨f₀, hf₀, hf₀v, hf₀im⟩ := exists_cylinder_map_pullback outer houter hOU f hf
  obtain ⟨f₁, hf₁, hf₁v, hf₁im⟩ := exists_cylinder_map_pullback H hH Subset.rfl a ha
  obtain ⟨f₂, hf₂, hf₂v, hf₂im⟩ := exists_cylinder_map_pullback inner hinner hIU f hf
  have hseam₀ (u : Q) : f₀ (u, 1) = f₁ (q₀ u, -1) := by
    rw [hf₀v ⟨(u, 1), u.property, by norm_num, le_rfl⟩,
      hf₁v ⟨(q₀ u, -1), (q₀ u).property, le_rfl, by norm_num⟩,
      ha0 _ ((hH0 _).mp rfl)]
    exact congrArg f (hq₀v u).symm
  have hseam₁ (u : Q) : f₁ (u, 1) = f₂ (q₁ u, -1) := by
    rw [hf₁v ⟨(u, 1), u.property, by norm_num, le_rfl⟩,
      hf₂v ⟨(q₁ u, -1), (q₁ u).property, le_rfl, by norm_num⟩,
      ha1 _ ((hH1 _).mp rfl)]
    exact congrArg f (hq₁v u).symm
  obtain ⟨g, j₀, j₁, j₂, hg, hj₀, hj₁, hj₂, hv₀, hv₁, hv₂, hgv₀, hgv₁, hgv₂,
    hg0, hg1, hgimage⟩ :=
    exists_three_cylinder_map_gluing e hcompat f₀ f₁ f₂ hf₀ hf₁ hf₂
      q₀ q₁ hq₀ hq₁ hseam₀ hseam₁
  refine ⟨a, g, outer.symm.trans j₀, H.symm.trans j₁, inner.symm.trans j₂,
    q₀.trans q₁, haemb, ha, hasub, hg,
    houter.symm.trans hj₀, hH.symm.trans hj₁, hinner.symm.trans hj₂,
    hq₀.trans hq₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change g (j₀ (outer.symm x)) = f x
    rw [hgv₀, hf₀v, outer.apply_symm_apply]
  · intro x
    change g (j₁ (H.symm x)) = a x
    rw [hgv₁, hf₁v, H.apply_symm_apply]
  · intro x
    change g (j₂ (inner.symm x)) = f x
    rw [hgv₂, hf₂v, inner.apply_symm_apply]
  · intro u
    exact (hg0 u).trans (hf₀v ⟨(u, -1), u.property, le_rfl, by norm_num⟩)
  · intro u
    exact (hg1 u).trans (hf₂v ⟨(q₁ (q₀ u), 1), (q₁ _).property, by norm_num, le_rfl⟩)
  · exact hgimage.trans (congrArg₂ (fun T W : Set X ↦ T ∪ W)
      (congrArg₂ (fun T W : Set X ↦ T ∪ W) hf₀im hf₁im) hf₂im)
  · intro x
    exact congrArg Prod.snd (hv₀ (outer.symm x))
  · intro x
    change (j₁ (H.symm x)).val.2 = _ ↔ _
    rw [hv₁]
    have hh := hH0 (H.symm x)
    rw [H.apply_symm_apply] at hh
    exact (show ((H.symm x).val.2 - 1) / 4 = -(1 / 2 : ℝ) ↔
      (H.symm x).val.2 = -1 by constructor <;> intro h <;> linarith).trans hh
  · intro x
    change (j₁ (H.symm x)).val.2 = _ ↔ _
    rw [hv₁]
    have hh := hH1 (H.symm x)
    rw [H.apply_symm_apply] at hh
    exact (show ((H.symm x).val.2 - 1) / 4 = 0 ↔
      (H.symm x).val.2 = 1 by constructor <;> intro h <;> linarith).trans hh
  · intro x
    exact congrArg Prod.snd (hv₂ (inner.symm x))

theorem exists_resolving_annulus_with_retained_exteriors
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (hb : 0 < b) (hbd : b < d)
    (A : Fin 2 → Set E) (c : ∀ k, squareAnnulus L d ≃ₜ A k)
    (hc : ∀ k, (c k).IsFinitePL) (j : Fin 2)
    {O I U : Set E} (outer : Cyl ≃ₜ O) (inner : Cyl ≃ₜ I)
    (houter : outer.IsFinitePL) (hinner : inner.IsFinitePL)
    (hOU : O ⊆ U) (hIU : I ⊆ U)
    (hOA : ∀ x : Cyl, (outer x : E) ∈ A j ↔ x.val.2 = 1)
    (hAO : ∀ p : squareAnnulus L d, (c j p : E) ∈ O ↔ depth L p = -d)
    (hAI : ∀ p : squareAnnulus L d, (c j.rev p : E) ∈ I ↔ depth L p = d)
    (hIA : ∀ x : Cyl, (inner x : E) ∈ A j.rev ↔ x.val.2 = -1)
    (f : E → X) (hf : PolyhedralPLInCharts e f U) (τ : (P2 × ℝ) → X)
    (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hvalue : ∀ (k : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L))
      (u : Icc (-d) d),
      f (c k ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) = τ (sourceTubeDiagonal k u, s)) :
    ∃ (a : P2 → X) (g : (V2 × ℝ) → X)
      (copyO : O ≃ₜ Left) (copyA : squareAnnulus L d ≃ₜ Middle)
      (copyI : I ≃ₜ Right) (q : Q ≃ₜ Q),
      Topology.IsEmbedding (fun p : squareAnnulus L d ↦ a p) ∧
      PolyhedralPLInCharts e a (squareAnnulus L d) ∧
      a '' squareAnnulus L d ⊆ τ '' identityTube L d ∧
      PolyhedralPLInCharts e g Cyl ∧
      copyO.IsFinitePL ∧ copyA.IsFinitePL ∧ copyI.IsFinitePL ∧ q.IsFinitePL ∧
      (∀ x : O, g (copyO x) = f x) ∧
      (∀ x : squareAnnulus L d, g (copyA x) = a x) ∧
      (∀ x : I, g (copyI x) = f x) ∧
      (∀ u : Q, g (u, -1) =
        f (outer ⟨(u, -1), u.property, le_rfl, by norm_num⟩)) ∧
      (∀ u : Q, g (u, 1) =
        f (inner ⟨(q u, 1), (q u).property, by norm_num, le_rfl⟩)) ∧
      g '' Cyl = (f '' O ∪ a '' squareAnnulus L d) ∪ f '' I := by
  obtain ⟨a, g, copyO, copyA, copyI, q, haemb, ha, hasub, hg,
    hO, hA, hI, hq, hvO, hvA, hvI, h0, h1, himage, _⟩ :=
    exists_resolving_annulus_with_retained_exteriors_and_levels e hcompat hd hwidth hb hbd
      A c hc j outer inner houter hinner hOU hIU hOA hAO hAI hIA f hf τ hτ hfib hvalue
  exact ⟨a, g, copyO, copyA, copyI, q, haemb, ha, hasub, hg,
    hO, hA, hI, hq, hvO, hvA, hvI, h0, h1, himage⟩

end PoincareConjecture.M76.Dehn.Annuli
