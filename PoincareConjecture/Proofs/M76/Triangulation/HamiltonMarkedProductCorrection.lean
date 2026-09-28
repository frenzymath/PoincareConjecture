import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPositiveMarkedExtension
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedProductPasting
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPrescribedMeridianBand
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProductBandReflection
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneDiskProduct










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-(1 / 4 : ℝ)) (1 / 4)
local notation "Io" => Ioo (-(1 / 4 : ℝ)) (1 / 4)

private theorem joined_map_of_oriented_band {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {R D : Set E} {b : D2 ≃ₜ D} (P : HamiltonUnmarkedDiskProduct R b)
    (hb : b.IsFinitePL) (F : (V2 × ℝ) → E)
    (hF : FinitePiecewiseAffineOn F (Q2 ×ˢ I)) (hFi : InjOn F (Q2 ×ˢ I))
    (hFm : MapsTo F (Q2 ×ˢ I) (frontier R))
    (hcenter : ∀ x ∈ Q2, F (x, 0) = P.map (x, 0))
    (hopen : IsOpen ((Subtype.val : frontier R → E) ⁻¹' (F '' (Q2 ×ˢ Io))))
    {w : ℝ} (hw : 0 < w) (hws : w ≤ 1 / 4)
    (hband : MapsTo F (Q2 ×ˢ Icc (-w) w) (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1)))
    (hpos : MapsTo F (Q2 ×ˢ Icc 0 w) (P.map '' (Q2 ×ˢ Ico (0 : ℝ) 1)))
    (hneg : MapsTo (F ∘ diskTimeReflection) (Q2 ×ˢ Icc 0 w)
      (P.reflected.map '' (Q2 ×ˢ Ico (0 : ℝ) 1))) :
    ∃ g : (V2 × ℝ) → E,
      FinitePiecewiseAffineOn g (D2 ×ˢ Icc (-w) w) ∧
      InjOn g (D2 ×ˢ Icc (-w) w) ∧ MapsTo g (D2 ×ˢ Icc (-w) w) R ∧
      (∀ p ∈ D2 ×ˢ Icc (-w) w, g p ∈ frontier R ↔ p.1 ∈ Q2) ∧
      (∀ x ∈ Q2, ∀ t ∈ Icc (-w) w, g (x, t) = F (x, t)) ∧
      ∀ x : D2, g ((x : V2), 0) = b x := by
  obtain ⟨fp, hpp, hpi, hpm, hpc, hpl, hpb⟩ :=
    exists_positive_marked_half_extension P hb F hF hFi hFm hcenter hw hws hband hpos
  obtain ⟨hFn, hFni, hFnm, hnc, _, hnband⟩ :=
    prescribed_band_reflection_properties P F hF hFi hFm hcenter hopen hband
  obtain ⟨fn, hnp, hni, hnm, hncenter, hnl, hnb⟩ :=
    exists_positive_marked_half_extension P.reflected hb (F ∘ diskTimeReflection)
      hFn hFni hFnm hnc hw hws hnband hneg
  rw [P.reflected_positive_image] at hnm
  exact exists_joined_marked_product_map P F fp fn hw hpp hnp hpi hni hpm hnm
    hpc hncenter hpb hnb hpl hnl





theorem exists_marked_disk_product_of_unmarked
    {B D : Set W} {b : D2 ≃ₜ D}
    (P : HamiltonUnmarkedDiskProduct (complementaryRegion B) b)
    (a : W ≃ᴬ[ℝ] V3)
    (hR : PLDomain
      (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph)
      (a '' complementaryRegion B))
    (hb : b.IsFinitePL)
    (e : frontier squareShell ≃ₜ frontier (complementaryRegion B)) (he : e.IsFinitePL)
    (hboundary : ∀ (x : Q2) (hx : standardSquareMeridian x ∈ frontier squareShell),
      (b ⟨x, sphere_subset_closedBall x.property⟩ : W) =
        e ⟨standardSquareMeridian x, hx⟩) :
    Nonempty (HamiltonMarkedDiskProduct e) := by
  obtain ⟨F, hF, hFi, hFm, hcenter, hopen, hvalue⟩ :=
    exists_original_prescribed_product_band P e he hboundary
  obtain ⟨w, hw, hws, hband⟩ := exists_prescribed_band_width P a hR F hF hFm hcenter
  have hwsmall : w ≤ 1 / 4 := by linarith
  have hfinish (Q : HamiltonUnmarkedDiskProduct (complementaryRegion B) b)
      (hc : ∀ x ∈ Q2, F (x, 0) = Q.map (x, 0))
      (hbnd : MapsTo F (Q2 ×ˢ Icc (-w) w) (Q.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1)))
      (hp : MapsTo F (Q2 ×ˢ Icc 0 w) (Q.map '' (Q2 ×ˢ Ico (0 : ℝ) 1)))
      (hn : MapsTo (F ∘ diskTimeReflection) (Q2 ×ˢ Icc 0 w)
        (Q.reflected.map '' (Q2 ×ˢ Ico (0 : ℝ) 1))) :
      Nonempty (HamiltonMarkedDiskProduct e) := by
    obtain ⟨g, hg, hgi, hgm, hgb, hgl, _⟩ :=
      joined_map_of_oriented_band Q hb F hF hFi hFm hc hopen hw hwsmall hbnd hp hn
    refine ⟨{
      width := w
      width_pos := hw
      width_le := hwsmall
      map := g
      piecewiseAffine := hg
      injective := hgi
      inside := hgm
      proper := hgb
      lateral := ?_
      open_strip := isOpen_image_proper_finitePL_product a hR hw g hg hgi hgm hgb }⟩
    intro x t ht hs
    have hpI : ((x : V2), t) ∈ Q2 ×ˢ I :=
      ⟨x.property, by constructor <;> linarith [ht.1, ht.2]⟩
    exact (hgl x x.property t ht).trans (hvalue ((x : V2), t) hpI hs)
  rcases prescribed_band_half_images P F hF hFi hFm hcenter hopen hw hwsmall hband with
    ⟨hp, hn⟩ | ⟨hp, hn⟩
  · exact hfinish P hcenter hband hp hn
  · have hc : ∀ x ∈ Q2, F (x, 0) = P.reflected.map (x, 0) := by
      intro x hx
      change F (x, 0) = P.map (x, -(0 : ℝ))
      rw [neg_zero]
      exact hcenter x hx
    have hbnd : MapsTo F (Q2 ×ˢ Icc (-w) w)
        (P.reflected.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1)) := by
      rw [P.reflected_open_image]
      exact hband
    have hdouble : P.reflected.reflected.map = P.map := by
      funext p
      change P.map (p.1, - -p.2) = P.map p
      simp only [neg_neg, Prod.eta]
    apply hfinish P.reflected hc hbnd hp
    rwa [hdouble]

end PoincareConjecture.M76.HamiltonIndexOne
