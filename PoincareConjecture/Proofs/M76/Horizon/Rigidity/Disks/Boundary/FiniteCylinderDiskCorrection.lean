import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Boundary.FiniteAnnularRimCorrection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.SquareAnnulusCylinder
import PoincareConjecture.Proofs.M76.Rigidity.SourceMeridianRim
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.StandardProperDisk

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open PoincareConjecture.M76.Dehn

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem OriginalFiniteCollarModel.exists_proper_disk_of_essential_cylindrical_rim
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (M : OriginalFiniteCollarModel e R)
    {T : Set (M.vertices → ℝ × V3)} (c : (Q2 ×ˢ I) ≃ₜ T) (hc : c.IsFinitePL)
    (hT : T ⊆ M.boundary.space)
    (j : V2 → (M.vertices → ℝ × V3)) (hj : FinitePiecewiseAffineOn j D2)
    (hi : InjOn j D2) (hjK : MapsTo j D2 M.complex.space)
    (rim : C(Q2, T)) (hjb : ∀ x : Q2, j x = (rim x : M.vertices → ℝ × V3))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map rim.continuous)) ≠ 1)
    (hheight : ∀ x : Q2, (c.symm (rim x) : V2 × ℝ).2 ∈ Ioo (-1 : ℝ) 1) :
    ∃ (D S : Set (M.vertices → ℝ × V3)) (gamma : Q2 ≃ₜ S),
      IsFinitePLBallPair V2 D S ∧ D ⊆ M.complex.space ∧
      D ∩ M.boundary.space = S ∧ gamma.IsFinitePL ∧
      ∀ x : Q2, (gamma x : M.vertices → ℝ × V3) =
        (c ⟨((x : V2), 0), x.property, by norm_num⟩ : M.vertices → ℝ × V3) := by
  classical
  obtain ⟨C, hC, hCheight⟩ := exists_finitePL_square_annulus_cylinder
  let a := C.trans c
  have hadepth (x : Q2) :
      depth 1 (a.symm (rim x)) ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8) := by
    have hh := hCheight (a.symm (rim x))
    have hCa : C (a.symm (rim x)) = c.symm (rim x) := by
      simp [a]
    rw [hCa] at hh
    have hx := hheight x
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨D, hD, hDK, hfront⟩ := M.exists_proper_disk_of_essential_annular_rim
    a (hC.trans hc) hT j hj hi hjK rim hjb hessential hadepth
  obtain ⟨f, hf, hfval⟩ := hc
  let zeroSection : V2 →ᴬ[ℝ] V2 × ℝ :=
    (ContinuousAffineMap.id ℝ V2).prod (ContinuousAffineMap.const ℝ V2 0)
  obtain ⟨K, hK, hKQ⟩ := exists_finite_hamiltonMeridianRim
  have hzPL : FinitePiecewiseAffineOn zeroSection Q2 :=
    hKQ ▸ (K.affineOnFaces_affine zeroSection).finitePiecewiseAffineOn hK
  have hzmap : MapsTo zeroSection Q2 (Q2 ×ˢ I) := by
    intro x hx
    exact ⟨hx, by norm_num [zeroSection]⟩
  let g : V2 → (M.vertices → ℝ × V3) := f ∘ zeroSection
  have hg : FinitePiecewiseAffineOn g Q2 := hf.comp hzPL hzmap
  have hgval (x : Q2) : g x =
      (c ⟨((x : V2), 0), x.property, by norm_num⟩ : M.vertices → ℝ × V3) :=
    (hfval ⟨zeroSection x, hzmap x.property⟩).symm
  have hgi : InjOn g Q2 := by
    intro x hx y hy hxy
    rw [hgval ⟨x, hx⟩, hgval ⟨y, hy⟩] at hxy
    have heq := c.injective (Subtype.ext hxy)
    exact congrArg (fun z : Q2 ×ˢ I => (z : V2 × ℝ).1) heq
  obtain ⟨gamma, hgamma, hgammaval⟩ := hg.exists_homeomorph_image hgi
  have hST : g '' Q2 ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hgval ⟨x, hx⟩]
    exact (c ⟨(x, 0), hx, by norm_num⟩).property
  have hcore (p : squareAnnulus 1 (1 / 8 : ℝ)) :
      (a p : M.vertices → ℝ × V3) ∈ g '' Q2 ↔ depth 1 p = 0 := by
    constructor
    · rintro ⟨x, hx, heq⟩
      rw [hgval ⟨x, hx⟩] at heq
      have hz := c.injective (Subtype.ext heq)
      have ht := congrArg (fun z : Q2 ×ˢ I => (z : V2 × ℝ).2) hz
      change (0 : ℝ) = (C p : V2 × ℝ).2 at ht
      linarith [hCheight p]
    · intro hp
      have ht : (C p : V2 × ℝ).2 = 0 := by rw [hCheight, hp]; ring
      refine ⟨(C p : V2 × ℝ).1, (C p).property.1, ?_⟩
      rw [hgval ⟨_, (C p).property.1⟩]
      apply congrArg Subtype.val
      apply congrArg c
      apply Subtype.ext
      exact Prod.ext rfl ht.symm
  have hmiddle := annulusChartImage_middle_circle hST a hcore
  rw [hmiddle] at hD hfront
  exact ⟨D, g '' Q2, gamma, hD, hDK, hfront, hgamma,
    fun x => (hgammaval x).trans (hgval x)⟩

end PoincareConjecture.M76
