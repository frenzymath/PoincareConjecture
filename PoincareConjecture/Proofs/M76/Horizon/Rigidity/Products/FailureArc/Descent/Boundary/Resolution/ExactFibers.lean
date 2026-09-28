import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Strips.ExteriorCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.ResolutionCopies
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.ProperCopies
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionStripBoundary

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

private theorem chart_mem_arm_iff {E : Set P2} (H : Sq ≃ₜ E)
    {c : P2 → P2} {u k : ℝ} (hk : k ∈ I)
    (hside : ∀ t : I, (H ⟨(k, t), hk, t.property⟩ : P2) = c (t, u)) (z : Sq) :
    (H z : P2) ∈ c '' arm u ↔ (z : P2).1 = k := by
  constructor
  · rintro ⟨w, hw, he⟩
    have he' : (H ⟨(k, w.1), hk, hw.1⟩ : P2) = H z := by
      rw [hside ⟨w.1, hw.1⟩]
      have hw' : (w.1, u) = w := Prod.ext rfl hw.2.symm
      exact (congrArg c hw').trans he
    exact (congrArg (fun t : Sq ↦ (t : P2).1) (H.injective (Subtype.ext he'))).symm
  · intro hz
    have he : z = ⟨(k, z.val.2), hk, z.property.2⟩ := Subtype.ext (Prod.ext hz rfl)
    rw [he, hside ⟨z.val.2, z.property.2⟩]
    exact ⟨(z.val.2, u), ⟨z.property.2, rfl⟩, rfl⟩

theorem exists_original_spanning_resolution_exact_fibers
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {S T : Set P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (c : Bool → P2 → P2)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source)
    (hcin : ∀ i, MapsTo (c i) source (T \ interior S))
    (houter : ∀ i z, z ∈ source → (c i z ∈ frontier T ↔ z.1 = 0))
    (hinner : ∀ i z, z ∈ source → (c i z ∈ frontier S ↔ z.1 = 1))
    (hdis : Disjoint (c false '' source) (c true '' source))
    {f : P2 → X} {τ : C3 → X}
    (hf : PolyhedralPLInCharts e f (T \ interior S))
    (hτ : PolyhedralPLInCharts e τ tube) (hτi : InjOn τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfull : (T \ interior S) ∩ f ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source)
    {R : Set X} (mark : Bool → Set X)
    (hfR : MapsTo f (T \ interior S) R) (hτR : MapsTo τ tube R)
    (hffront : ∀ x ∈ T \ interior S,
      f x ∈ frontier R ↔ x ∈ frontier T ∨ x ∈ frontier S)
    (hτfront : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1)
    (hfouter : ∀ x ∈ T \ interior S, x ∈ frontier T → f x ∈ mark false)
    (hfinner : ∀ x ∈ T \ interior S, x ∈ frontier S → f x ∈ mark true)
    (hτbottom : ∀ z ∈ tube, z.2 = 0 → τ z ∈ mark false)
    (hτtop : ∀ z ∈ tube, z.2 = 1 → τ z ∈ mark true) :
    ∃ (positive : Bool → Bool) (E : Fin 2 → Set P2) (H : ∀ j, Sq ≃ₜ E j)
      (p : Fin 2 → P2 → P2) (g : Fin 2 → P2 → X),
      let sign := fun (j : Fin 2) (i : Bool) ↦ if j = 0 then positive i else !(positive i)
      let τ' := fun j ↦ τ ∘ tubeArmOrientation (!(sign j false)) (!(sign j true))
      ∃ C : ∀ j, AnnulusSquareCopies ![f ∘ p j, τ' j ∘ resolvingSquare true] (g j),
      (∀ j, (H j).IsFinitePL) ∧ (∀ j z, (H j z : P2) = p j z) ∧
      (∀ j, E j ⊆ T \ interior S) ∧ Disjoint (E 0) (E 1) ∧
      (c false '' source ∪ c true '' source) ∪ (E 0 ∪ E 1) = T \ interior S ∧
      (∀ j i, E j ∩ (c i '' source) = c i '' arm (farArmParameter (sign j i))) ∧
      (∀ j (t : I), (H j ⟨(0, t), by norm_num, t.property⟩ : P2) =
        c false (t, farArmParameter (sign j false))) ∧
      (∀ j (t : I), (H j ⟨(1, t), by norm_num, t.property⟩ : P2) =
        c true (t, farArmParameter (sign j true))) ∧
      (∀ j, PolyhedralPLInCharts e (g j) (squareAnnulus 8 1)) ∧
      (∀ j (z : Sq), (H j z : P2) ∈ frontier T ↔ (z : P2).2 = 0) ∧
      (∀ j (z : Sq), (H j z : P2) ∈ frontier S ↔ (z : P2).2 = 1) ∧
      (∀ j, MapsTo (g j) (squareAnnulus 8 1) R) ∧
      (∀ j z, z ∈ squareAnnulus 8 1 →
        (g j z ∈ frontier R ↔ depth 8 z = -1 ∨ depth 8 z = 1)) ∧
      (∀ j z, z ∈ squareAnnulus 8 1 → depth 8 z = -1 → g j z ∈ mark false) ∧
      (∀ j z, z ∈ squareAnnulus 8 1 → depth 8 z = 1 → g j z ∈ mark true) ∧
      ∀ j, {x : P2 | x ∈ squareAnnulus 8 1 ∧
        ∃ y ∈ squareAnnulus 8 1, y ≠ x ∧ g j y = g j x} =
        (fun z : Sq ↦ ((C j).chart 0 z : P2)) ''
          {u : Sq | ∃ v : Sq, v ≠ u ∧ f (H j v) = f (H j u)} := by
  classical
  obtain ⟨positive, E, H, hH, hES, hEdis, hcover, hcontact, hHl, hHr, hHo, hHi⟩ :=
    exists_spanning_strip_exterior_square_charts hS hT hST c hcPL hci hcin houter hinner hdis
  let sign (j : Fin 2) (i : Bool) := if j = 0 then positive i else !(positive i)
  let τ' (j : Fin 2) := τ ∘ tubeArmOrientation (!(sign j false)) (!(sign j true))
  have hH' := hH
  choose p hp hpval using hH'
  have hpS (j : Fin 2) : MapsTo (p j) Sq (T \ interior S) := by
    intro z hz
    rw [← hpval j ⟨z, hz⟩]
    exact hES j (H j ⟨z, hz⟩).property
  have hd (j : Fin 2) : PolyhedralPLInCharts e (f ∘ p j) Sq := by
    obtain ⟨K, hK, hKs, hAff⟩ := hp j
    simpa only [hKs] using hf.comp_finitePiecewiseAffineOn K hK
      ⟨K, hK, rfl, hAff⟩ (hKs.symm ▸ hpS j)
  have heqs (j : Fin 2) :
      (∀ t : I, (f ∘ p j) (0, t) = τ' j (strip 0 true (t, -1))) ∧
      (∀ t : I, (f ∘ p j) (1, t) = τ' j (strip 0 true (t, 1))) := by
    have hcorners := reoriented_tube_old_arm_equations f (c false) (c true) τ h0 h1
      (!(sign j false)) (!(sign j true))
    constructor
    · intro t
      rw [Function.comp_apply, ← hpval j ⟨(0, t), by norm_num, t.property⟩, hHl j t]
      simpa only [Bool.not_not, strip, signedHeight, height, Bool.true_eq, ↓reduceIte,
        abs_neg, abs_one, max_eq_left (show (0 : ℝ) ≤ 1 by norm_num)] using (hcorners t).1
    · intro t
      rw [Function.comp_apply, ← hpval j ⟨(1, t), by norm_num, t.property⟩, hHr j t]
      simpa only [Bool.not_not, strip, signedHeight, height, Bool.true_eq, ↓reduceIte,
        abs_one, max_eq_left (show (0 : ℝ) ≤ 1 by norm_num)] using (hcorners t).2.2.2
  have hex (j : Fin 2) : ∃ g : P2 → X, PolyhedralPLInCharts e g (squareAnnulus 8 1) ∧
      Nonempty (AnnulusSquareCopies ![f ∘ p j, τ' j ∘ resolvingSquare true] g) :=
    exists_resolving_annulus_with_copies hcompat (hd j)
      (reoriented_tube_polyhedralPL e hτ _ _) true (heqs j).1 (heqs j).2
  choose g hg hC using hex
  let C (j : Fin 2) := (hC j).some
  have hproper (j : Fin 2) : MapsTo (g j) (squareAnnulus 8 1) R ∧
      (∀ z ∈ squareAnnulus 8 1,
        g j z ∈ frontier R ↔ depth 8 z = -1 ∨ depth 8 z = 1) ∧
      (∀ z ∈ squareAnnulus 8 1, depth 8 z = -1 → g j z ∈ mark false) ∧
      (∀ z ∈ squareAnnulus 8 1, depth 8 z = 1 → g j z ∈ mark true) := by
    have hq (z : P2) (hz : z ∈ Sq) :
        tubeArmOrientation (!(sign j false)) (!(sign j true)) (resolvingSquare true z) ∈ tube :=
      (tubeArmOrientation_mem_tube _ _ _).mpr (resolvingSquare_mapsTo true hz)
    apply (C j).proper_marked mark
    · intro k
      fin_cases k
      · exact hfR.comp (hpS j)
      · exact fun z hz ↦ hτR (hq z hz)
    · intro k z
      fin_cases k
      · change f (p j z) ∈ frontier R ↔ _
        rw [hffront _ (hpS j z.property), ← hpval j z, hHo j z, hHi j z]
      · change τ (tubeArmOrientation _ _ (resolvingSquare true z)) ∈ frontier R ↔ _
        rw [hτfront _ (hq z z.property), tubeArmOrientation_longitudinal]
        rfl
    · intro k t
      fin_cases k
      · change f (p j (t, 0)) ∈ mark false
        rw [← hpval j ⟨(t, 0), t.property, by norm_num⟩]
        exact hfouter _ (hES j (H j _).property) ((hHo j _).mpr rfl)
      · apply hτbottom _ (hq (t, 0) ⟨t.property, by norm_num⟩)
        rw [tubeArmOrientation_longitudinal]
        rfl
    · intro k t
      fin_cases k
      · change f (p j (t, 1)) ∈ mark true
        rw [← hpval j ⟨(t, 1), t.property, by norm_num⟩]
        exact hfinner _ (hES j (H j _).property) ((hHi j _).mpr rfl)
      · apply hτtop _ (hq (t, 1) ⟨t.property, by norm_num⟩)
        rw [tubeArmOrientation_longitudinal]
        rfl
  refine ⟨positive, E, H, p, g, C, hH, hpval, hES, hEdis, hcover,
    hcontact, hHl, hHr, hg, hHo, hHi, fun j ↦ (hproper j).1,
    fun j ↦ (hproper j).2.1, fun j ↦ (hproper j).2.2.1,
    fun j ↦ (hproper j).2.2.2, ?_⟩
  intro j
  have hpre (z : Sq) : (f ∘ p j) z ∈ τ' j '' tube ↔
      (z : P2).1 = 0 ∨ (z : P2).1 = 1 := by
    rw [show τ' j '' tube = τ '' tube from reoriented_tube_image τ _ _]
    rw [Function.comp_apply, ← hpval j z]
    have hretained := retained_tube_preimage hfull (hES j) (hcontact j false) (hcontact j true)
    have hzE := (H j z).property
    have hmem : f (H j z) ∈ τ '' tube ↔
        (H j z : P2) ∈ (c false '' arm (farArmParameter (sign j false))) ∪
          (c true '' arm (farArmParameter (sign j true))) := by
      constructor
      · intro hz
        exact hretained.subset ⟨hzE, hz⟩
      · intro hz
        exact (hretained.symm.subset hz).2
    rw [hmem, mem_union, chart_mem_arm_iff (H j) (by norm_num) (hHl j),
      chart_mem_arm_iff (H j) (by norm_num) (hHr j)]
  have hτ'i : InjOn (τ' j) tube := by
    intro x hx y hy hxy
    exact tubeArmOrientation_injective _ _ (hτi
      ((tubeArmOrientation_mem_tube _ _ x).mpr hx)
      ((tubeArmOrientation_mem_tube _ _ y).mpr hy) hxy)
  have hdoubles := resolving_copies_double_points true (C j) hτ'i hpre (heqs j).1 (heqs j).2
  simpa only [Function.comp_apply, ← hpval j] using hdoubles

end PoincareConjecture.M76.Dehn
