import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Cup.ArmIdentification



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryCup

open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_original_boundary_cup_map
    {X ι E F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {c₀ : P2 → E} {c₁ : P2 → F}
    (hc₀ : FinitePiecewiseAffineOn c₀ source) (hi₀ : InjOn c₀ source)
    (hc₁ : FinitePiecewiseAffineOn c₁ source) (hi₁ : InjOn c₁ source)
    {D U Q : Set E} {B V : Set F}
    (hD : IsFinitePLBallPair P2 D (U ∪ c₀ '' arm 0))
    (hB : IsFinitePLBallPair P2 B (V ∪ c₁ '' arm 1))
    (hU : IsFinitePLBallPair ℝ U {c₀ (0, 0), c₀ (1, 0)})
    (hV : IsFinitePLBallPair ℝ V {c₁ (0, 1), c₁ (1, 1)})
    (hUW : U ∩ (c₀ '' arm 0) = {c₀ (0, 0), c₀ (1, 0)})
    (hVZ : V ∩ (c₁ '' arm 1) = {c₁ (0, 1), c₁ (1, 1)})
    (hcontact : D ∩ (c₀ '' halfSource false) = c₀ '' arm 0)
    (houter : D ∩ Q = U)
    (hcQ : ∀ p ∈ source, c₀ p ∈ Q ↔ p.1 = 0 ∨ p.1 = 1)
    (f₀ : E → X) (f₁ : F → X) (hf₁ : PolyhedralPLInCharts e f₁ B) (hi₁f : InjOn f₁ B)
    {τ : C3 → X} (hτ : PolyhedralPLInCharts e τ tube) (hτi : InjOn τ tube)
    {A T R : Set X} (hBA : f₁ '' B ⊆ A) (hBT : Disjoint (f₁ '' B) T)
    (hA : ∀ z ∈ tube, τ z ∈ A ↔ z.1.2 = z.1.1)
    (hT : ∀ z ∈ tube, τ z ∈ T ↔ z.1.2 = -z.1.1)
    (hBR : MapsTo f₁ B R) (hτR : MapsTo τ tube R)
    (hBfront : ∀ x ∈ B, f₁ x ∈ frontier R ↔ x ∈ V)
    (hτfront : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (hfar₀ : ∀ t : I, f₀ (c₀ ((t : ℝ), -1)) = τ ((-1, 1), (t : ℝ)))
    (hfar₁ : ∀ t : I, f₁ (c₁ ((t : ℝ), 1)) = τ ((1, 1), (t : ℝ))) :
    ∃ v : E → X, PolyhedralPLInCharts e v (D ∪ c₀ '' halfSource false) ∧
      InjOn v (D ∪ c₀ '' halfSource false) ∧ EqOn v f₀ (c₀ '' arm (-1)) ∧
      (v '' (D ∪ c₀ '' halfSource false)) ∩ A = f₁ '' B ∧
      (v '' (D ∪ c₀ '' halfSource false)) ∩ T = f₀ '' (c₀ '' arm (-1)) ∧
      v '' (D ∪ c₀ '' halfSource false) = f₁ '' B ∪
        τ '' ((Icc (-1 : ℝ) 1 ×ˢ {(1 : ℝ)}) ×ˢ I) ∧
      MapsTo v (D ∪ c₀ '' halfSource false) R ∧
      ∀ x ∈ D ∪ c₀ '' halfSource false, v x ∈ frontier R ↔ x ∈ Q := by
  obtain ⟨H, hH, hHcenter, hHU, _⟩ := exists_disk_identification_center_to_far_arm
    hc₀ hi₀ hc₁ hi₁ hD hB hU hV hUW hVZ
  obtain ⟨u, hu, huval⟩ := hH
  have humap : MapsTo u D B := by
    intro x hx
    rw [← huval ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hui : InjOn u D := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((huval ⟨x, hx⟩).trans (hxy.trans (huval ⟨y, hy⟩).symm))))
  have huimage : u '' D = B := by
    apply Subset.antisymm humap.image_subset
    intro x hx
    obtain ⟨y, hy⟩ := H.surjective ⟨x, hx⟩
    exact ⟨y, y.property, (huval y).symm.trans (congrArg Subtype.val hy)⟩
  have hucenter (t : I) (hx : c₀ ((t : ℝ), 0) ∈ D) :
      u (c₀ ((t : ℝ), 0)) = c₁ ((t : ℝ), 1) :=
    (huval ⟨_, hx⟩).symm.trans (hHcenter t hx)
  obtain ⟨g, hg, hgi, hgval, hgimage⟩ := exists_original_bridge_on_source_half hτ hτi hc₀ hi₀
  obtain ⟨K, hK, hKD, hKu⟩ := hu
  have hcore : PolyhedralPLInCharts e (f₁ ∘ u) K.space :=
    hf₁.comp_finitePiecewiseAffineOn K hK ⟨K, hK, rfl, hKu⟩
      (fun x hx ↦ humap (hKD.subset hx))
  have hhalf := ((isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
    (isFinitePLBallPair_Icc (show (-1 : ℝ) < 0 by norm_num))).image_of_subset
      hc₀ (halfSource_subset_source false) hi₀
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ := hhalf
  change L.space = c₀ '' halfSource false at hLs
  have hbridge : PolyhedralPLInCharts e g L.space := by rw [hLs]; exact hg
  have hcenter (x : E) (hx : x ∈ D) (hy : x ∈ c₀ '' halfSource false) :
      (f₁ ∘ u) x = g x := by
    obtain ⟨p, hp, rfl⟩ := hcontact.subset ⟨hx, hy⟩
    have hp0 : p.2 = 0 := hp.2
    have hpEq : p = (p.1, 0) := Prod.ext rfl hp0
    rw [hpEq] at hx ⊢
    rw [Function.comp_apply, hucenter ⟨_, hp.1⟩ hx, hfar₁ ⟨_, hp.1⟩,
      hgval _ (show (p.1, 0) ∈ halfSource false from ⟨hp.1, by norm_num⟩)]
    simp only [bridgeCoordinates_apply, mul_zero, zero_add]
  obtain ⟨v, hv, hvD, hvH⟩ := _root_.Dehn.exists_circle_attachment_map_union he K L hK hL
    hcore hbridge (fun x hx hy ↦ hcenter x (hKD.subset hx) (hLs.subset hy))
  have hvD' : EqOn v (f₁ ∘ u) D := hKD ▸ hvD
  have hvH' : EqOn v g (c₀ '' halfSource false) := hLs ▸ hvH
  have hvPL : PolyhedralPLInCharts e v (D ∪ c₀ '' halfSource false) := by
    simpa only [hKD, hLs] using hv
  have hbridgeA (p : P2) (hp : p ∈ halfSource false) : g (c₀ p) ∈ A ↔ p.2 = 0 := by
    rw [hgval p hp, hA _ (bridgeCoordinates_mapsTo hp)]
    change 1 = 2 * p.2 + 1 ↔ p.2 = 0
    constructor <;> intro h <;> linarith
  have hbridgeT (p : P2) (hp : p ∈ halfSource false) : g (c₀ p) ∈ T ↔ p.2 = -1 := by
    rw [hgval p hp, hT _ (bridgeCoordinates_mapsTo hp)]
    change 1 = -(2 * p.2 + 1) ↔ p.2 = -1
    constructor <;> intro h <;> linarith
  have hcross (x y : E) (hx : x ∈ D) (hy : y ∈ c₀ '' halfSource false)
      (hxy : v x = v y) : x = y := by
    obtain ⟨p, hp, rfl⟩ := hy
    have hpA : g (c₀ p) ∈ A := by
      rw [← hvH' ⟨p, hp, rfl⟩, ← hxy, hvD' hx]
      exact hBA ⟨u x, humap hx, rfl⟩
    have hp0 := (hbridgeA p hp).mp hpA
    have hyD : c₀ p ∈ D := (hcontact.superset ⟨p, ⟨hp.1, hp0⟩, rfl⟩).1
    exact hui hx hyD (hi₁f (humap hx) (humap hyD)
      ((hvD' hx).symm.trans (hxy.trans (hvD' hyD))))
  have hvi : InjOn v (D ∪ c₀ '' halfSource false) := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hui hx hy (hi₁f (humap hx) (humap hy)
        ((hvD' hx).symm.trans (hxy.trans (hvD' hy))))
    · exact hcross x y hx hy hxy
    · exact (hcross y x hy hx hxy.symm).symm
    · exact hgi hx hy ((hvH' hx).symm.trans (hxy.trans (hvH' hy)))
  have hfarH : c₀ '' arm (-1) ⊆ c₀ '' halfSource false := by
    apply image_mono
    intro p hp
    exact ⟨hp.1, by rw [show p.2 = -1 from hp.2]; norm_num⟩
  have hkeep : EqOn v f₀ (c₀ '' arm (-1)) := by
    rintro x ⟨p, hp, rfl⟩
    rw [hvH' (hfarH ⟨p, hp, rfl⟩), hgval p (by
      exact ⟨hp.1, by rw [show p.2 = -1 from hp.2]; norm_num⟩)]
    have hpEq : p = (p.1, -1) := Prod.ext rfl hp.2
    rw [hpEq, hfar₀ ⟨_, hp.1⟩, bridgeCoordinates_apply]
    norm_num
  have himage : v '' (D ∪ c₀ '' halfSource false) = f₁ '' B ∪
      τ '' ((Icc (-1 : ℝ) 1 ×ˢ {(1 : ℝ)}) ×ˢ I) := by
    rw [image_union, image_congr hvD', image_comp, huimage, image_congr hvH', hgimage]
  refine ⟨v, hvPL, hvi, hkeep, ?_, ?_, himage, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro z ⟨⟨x, hx | hx, rfl⟩, hz⟩
      · exact ⟨u x, humap hx, (hvD' hx).symm⟩
      · obtain ⟨p, hp, rfl⟩ := hx
        have hp0 := (hbridgeA p hp).mp ((hvH' ⟨p, hp, rfl⟩) ▸ hz)
        have hxD := (hcontact.superset ⟨p, ⟨hp.1, hp0⟩, rfl⟩).1
        exact ⟨u (c₀ p), humap hxD, (hvD' hxD).symm⟩
    · intro z hz
      exact ⟨himage.superset (Or.inl hz), hBA hz⟩
  · apply Subset.antisymm
    · rintro z ⟨⟨x, hx | hx, rfl⟩, hz⟩
      · exact (Set.disjoint_left.mp hBT ⟨u x, humap hx, (hvD' hx).symm⟩ hz).elim
      · obtain ⟨p, hp, rfl⟩ := hx
        have hpfar := (hbridgeT p hp).mp ((hvH' ⟨p, hp, rfl⟩) ▸ hz)
        have hxFar : c₀ p ∈ c₀ '' arm (-1) := ⟨p, ⟨hp.1, hpfar⟩, rfl⟩
        exact ⟨c₀ p, hxFar, (hkeep hxFar).symm⟩
    · rintro z ⟨x, hx, rfl⟩
      refine ⟨⟨x, Or.inr (hfarH hx), hkeep hx⟩, ?_⟩
      obtain ⟨p, hp, rfl⟩ := hx
      rw [← hkeep ⟨p, hp, rfl⟩, hvH' (hfarH ⟨p, hp, rfl⟩)]
      exact (hbridgeT p (by exact ⟨hp.1, by rw [show p.2 = -1 from hp.2]; norm_num⟩)).mpr hp.2
  · intro x hx
    rcases hx with hx | hx
    · rw [hvD' hx]
      exact hBR (humap hx)
    · obtain ⟨p, hp, rfl⟩ := hx
      rw [hvH' ⟨p, hp, rfl⟩, hgval p hp]
      exact hτR (bridgeCoordinates_mapsTo hp)
  · intro x hx
    rcases hx with hx | hx
    · rw [hvD' hx, Function.comp_apply, hBfront _ (humap hx), ← huval ⟨x, hx⟩,
        ← hHU ⟨x, hx⟩, ← houter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hx, h⟩⟩
    · obtain ⟨p, hp, rfl⟩ := hx
      rw [hvH' ⟨p, hp, rfl⟩, hgval p hp, hτfront _ (bridgeCoordinates_mapsTo hp)]
      exact (hcQ p (halfSource_subset_source false hp)).symm

end PoincareConjecture.M76.Dehn.Annuli.BoundaryCup
