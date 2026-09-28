import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PrescribedIntervalDiskMap
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonalCrossingResolution

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)

noncomputable def resolutionMap (b : ℝ) (alternatePair positive : Bool) : P2 → C3 :=
  if alternatePair then alternate b positive else strip b positive

def stripRim : Set P2 :=
  ({0, 1} ×ˢ Icc (-1 : ℝ) 1) ∪ (Icc (0 : ℝ) 1 ×ˢ {-1, 1})

def arm (u : ℝ) : Set P2 := Icc (0 : ℝ) 1 ×ˢ {u}

theorem exists_arm_parameter (u : ℝ) :
    IsFinitePLBallPair ℝ (arm u) {(0, u), (1, u)} ∧
      ∃ p : I01 ≃ₜ arm u, p.IsFinitePL ∧ ∀ t : I01, (p t : P2) = ((t : ℝ), u) := by
  let A : ℝ →ᴬ[ℝ] P2 :=
    (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ u)
  have hinj : InjOn A I01 := by
    intro x _ y _ h
    exact congrArg Prod.fst h
  have himage : A '' I01 = arm u := by
    change (fun x : ℝ => (x, u)) '' I01 = I01 ×ˢ {u}
    exact (prod_singleton (s := I01) (b := u)).symm
  have hball : IsFinitePLBallPair ℝ (arm u) {(0, u), (1, u)} := by
    have h := isFinitePLBallPair_affine_interval zero_lt_one A hinj
    rw [himage] at h
    exact h
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hI
  have hA : FinitePiecewiseAffineOn A I01 :=
    ⟨K, hK, hKs, K.affineOnFaces_affine A⟩
  have hparam := hA.exists_homeomorph_image hinj
  rw [himage] at hparam
  obtain ⟨p, hp, hpval⟩ := hparam
  exact ⟨hball, p, hp, hpval⟩

theorem exists_disk_map_of_resolution_arm
    {E F X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {S Q W : Set E} {a z : E} (hS : IsFinitePLBallPair P2 S Q)
    (hW : IsFinitePLBallPair ℝ W {a, z}) (hWQ : W ⊆ Q) (haz : a ≠ z)
    (p0 : I01 ≃ₜ W) (hp0 : p0.IsFinitePL)
    (hp00 : (p0 (0 : unitInterval) : E) = a)
    (hp01 : (p0 (1 : unitInterval) : E) = z)
    {f : E → X} (hf : PolyhedralPLInCharts e f S)
    {τ : C3 → X} (hτ : PolyhedralPLInCharts e τ tube)
    {b u : ℝ} (hb : b < 1) (hu : u = -1 ∨ u = 1)
    (alternatePair positive : Bool)
    (hold : ∀ t : I01, f (p0 t) = τ (resolutionMap 0 alternatePair positive (t, u))) :
    ∃ (B : Set E) (C : Set P2) (n : S ≃ₜ TR) (m : source ≃ₜ TL) (g : P2 → X),
      IsFinitePLBallPair ℝ B {a, z} ∧
      IsFinitePLBallPair ℝ C {(0, u), (1, u)} ∧
      W ∪ B = Q ∧ W ∩ B = {a, z} ∧
      arm u ∪ C = stripRim ∧ arm u ∩ C = {(0, u), (1, u)} ∧
      n.IsFinitePL ∧ m.IsFinitePL ∧
      (∀ (t : I01) (x : source), (x : P2) = ((t : ℝ), u) →
        (n ⟨p0 t, hS.1 (hWQ (p0 t).property)⟩ : P2) = m x) ∧
      PolyhedralPLInCharts e g (TR ∪ TL) ∧
      (∀ x : S, g (n x) = f x) ∧
      (∀ x : source, g (m x) = τ (resolutionMap b alternatePair positive x)) ∧
      g '' (TR ∪ TL) = f '' S ∪ τ '' (resolutionMap b alternatePair positive '' source) ∧
      IsFinitePLBallPair P2 (TR ∪ TL)
        ((fun x : S => (n x : P2)) '' (Subtype.val ⁻¹' B) ∪
         (fun x : source => (m x : P2)) '' (Subtype.val ⁻¹' C)) ∧
      ∀ Z : Set X, (TR ∪ TL) ∩ g ⁻¹' Z =
        (fun x : S => (n x : P2)) '' {x : S | f x ∈ Z} ∪
        (fun x : source => (m x : P2)) ''
          {x : source | τ (resolutionMap b alternatePair positive x) ∈ Z} := by
  have hrect : IsFinitePLBallPair P2 source stripRim :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  obtain ⟨hArm, p1, hp1, hp1val⟩ := exists_arm_parameter u
  have hArmRim : arm u ⊆ stripRim := by
    intro x hx
    refine Or.inr ⟨hx.1, ?_⟩
    change x.2 = -1 ∨ x.2 = 1
    have hx2 : x.2 = u := hx.2
    rw [hx2]
    exact hu
  have hends : ((0, u) : P2) ≠ (1, u) := by
    intro h
    have h01 : (0 : ℝ) = 1 := congrArg Prod.fst h
    norm_num at h01
  have hres : FinitePiecewiseAffineOn (resolutionMap b alternatePair positive) source := by
    cases alternatePair with
    | false => exact (finitePiecewiseAffineOn_maps b positive).1
    | true => exact (finitePiecewiseAffineOn_maps b positive).2
  have hresTube : MapsTo (resolutionMap b alternatePair positive) source tube := by
    cases alternatePair with
    | false => exact (mapsTo_tube hb.le positive).1
    | true => exact (mapsTo_tube hb.le positive).2
  have hcopy := hres
  obtain ⟨K, hK, hKs, _⟩ := hcopy
  have hcomposite : PolyhedralPLInCharts e (τ ∘ resolutionMap b alternatePair positive)
      source := by
    have hr : FinitePiecewiseAffineOn (resolutionMap b alternatePair positive) K.space := by
      simpa only [hKs] using hres
    have hm : MapsTo (resolutionMap b alternatePair positive) K.space tube := by
      simpa only [hKs] using hresTube
    have h := hτ.comp_finitePiecewiseAffineOn K hK hr hm
    simpa only [hKs] using h
  have huabs : |u| = 1 := by rcases hu with rfl | rfl <;> norm_num
  have hretain (t : I01) : resolutionMap b alternatePair positive (t, u) =
      resolutionMap 0 alternatePair positive (t, u) := by
    have hbound : b ≤ |((t : ℝ), u).2| := by simpa only [huabs] using hb.le
    cases alternatePair with
    | false => exact (eq_zero_of_outer positive (t, u) hbound).1
    | true => exact (eq_zero_of_outer positive (t, u) hbound).2
  have hagree (t : I01) : f (p0 t) = (τ ∘ resolutionMap b alternatePair positive) (p1 t) := by
    change f (p0 t) = τ (resolutionMap b alternatePair positive (p1 t))
    rw [hp1val, hretain]
    exact hold t
  obtain ⟨B, C, n, m, p, g, hB, hC, hWB, hAC, hWBi, hACi,
      hn, hm, _, _, _, hnp, hmp, hg, hgn, hgm, himage, hrim, hpre⟩ :=
    exists_prescribed_interval_disk_map e hcompat hS hrect hW hArm hWQ hArmRim
      haz hends p0 p1 hp0 hp1 hp00 hp01 (hp1val 0) (hp1val 1) hf hcomposite hagree
  refine ⟨B, C, n, m, g, hB, hC, hWB, hWBi, hAC, hACi, hn, hm, ?_,
    hg, hgn, hgm, ?_, hrim, hpre⟩
  · intro t x hx
    have hsource : (⟨p1 t, hrect.1 (hArmRim (p1 t).property)⟩ : source) = x :=
      Subtype.ext ((hp1val t).trans hx.symm)
    have hxmap : (m x : P2) = p t := by
      simpa only [hsource] using hmp t
    exact (hnp t).trans hxmap.symm
  · simpa only [image_image, Function.comp_def] using himage

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
