import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Collars.RetainedCylinderCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Properness
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Fibers.TubeContacts



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)
local notation "Left" => Set.prod Q (Icc (-1 : ℝ) (-(1 / 2 : ℝ)))
local notation "Middle" => Set.prod Q (Icc (-(1 / 2 : ℝ)) 0)
local notation "Right" => Set.prod Q (Icc (0 : ℝ) 1)

variable {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
  (e : ι → OpenPartialHomeomorph X F)
  {l r L d : ℝ} {A : Fin 2 → Set P2}
  (B : ∀ k, OrientedPolygonCollar l r (A k)) (j : Fin 2)



structure NestedResolvingCylinder (f : P2 → X) (τ : (P2 × ℝ) → X) where
  outer : Cyl ≃ₜ (annulusSquare L (-d) \ (B j).outer.inside : Set P2)
  inner : Cyl ≃ₜ (closure (B j.rev).inner.inside \ interior (annulusSquare L d) : Set P2)
  outer_PL : outer.IsFinitePL
  inner_PL : inner.IsFinitePL
  outer_source : annulusSquare L (-d) \ (B j).outer.inside ⊆ squareAnnulus L d
  inner_source : closure (B j.rev).inner.inside \ interior (annulusSquare L d) ⊆
    squareAnnulus L d
  outer_end : ∀ x : Cyl, x.val.2 = -1 ↔ depth L (outer x : P2) = -d
  inner_end : ∀ x : Cyl, x.val.2 = 1 ↔ depth L (inner x : P2) = d
  outer_strict : ∀ x : (annulusSquare L (-d) \ (B j).outer.inside : Set P2), depth L x < d
  inner_strict : ∀ x : (closure (B j.rev).inner.inside \ interior (annulusSquare L d) : Set P2),
    -d < depth L x
  outer_contact : ∀ x : Cyl, (outer x : P2) ∈ A j ∪ A j.rev ↔ x.val.2 = 1
  inner_contact : ∀ x : Cyl, (inner x : P2) ∈ A j ∪ A j.rev ↔ x.val.2 = -1
  annulus : P2 → X
  map : (V2 × ℝ) → X
  copyO : (annulusSquare L (-d) \ (B j).outer.inside : Set P2) ≃ₜ Left
  copyA : squareAnnulus l r ≃ₜ Middle
  copyI : (closure (B j.rev).inner.inside \ interior (annulusSquare L d) : Set P2) ≃ₜ Right
  annulus_embedding : Topology.IsEmbedding (fun x : squareAnnulus l r ↦ annulus x)
  annulus_PL : PolyhedralPLInCharts e annulus (squareAnnulus l r)
  annulus_tube : annulus '' squareAnnulus l r ⊆ τ '' identityTube l r
  map_PL : PolyhedralPLInCharts e map Cyl
  copyO_PL : copyO.IsFinitePL
  copyA_PL : copyA.IsFinitePL
  copyI_PL : copyI.IsFinitePL
  keepO : ∀ x, map (copyO x) = f x
  keepA : ∀ x, map (copyA x) = annulus x
  keepI : ∀ x, map (copyI x) = f x
  image : map '' Cyl =
    (f '' (annulusSquare L (-d) \ (B j).outer.inside) ∪ annulus '' squareAnnulus l r) ∪
      f '' (closure (B j.rev).inner.inside \ interior (annulusSquare L d))
  copyO_level : ∀ x, (copyO x).val.2 = ((outer.symm x).val.2 - 3) / 4
  copyA_lower : ∀ x, (copyA x).val.2 = -(1 / 2 : ℝ) ↔ depth l x = -r
  copyA_upper : ∀ x, (copyA x).val.2 = 0 ↔ depth l x = r
  copyI_level : ∀ x, (copyI x).val.2 = ((inner.symm x).val.2 + 1) / 2
  middle_singleton : ∀ z ∈ Middle, ∀ w ∈ Cyl, map w = map z → w = z

theorem nonempty_nested_resolving_cylinder
    (hcompat : ∀ i k, (e i).symm.trans (e k) ∈ piecewiseAffineGroupoid F)
    (hr : 0 < r) (hwidth : 4 * r < l) {b : ℝ} (hb : 0 < b) (hbr : b < r)
    (hd : 0 < d) (hsourceWidth : 2 * d < L)
    (hA : ∀ k, A k ⊆ {p : P2 | -d < depth L p ∧ depth L p < d})
    (henclosing : annulusSquare L d ⊆ (B j.rev).outer.inside)
    (hnested : closure (B j.rev).outer.inside ⊆ (B j).inner.inside)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f (squareAnnulus L d))
    (τ : (P2 × ℝ) → X) (hτ : PolyhedralPLInCharts e τ (identityTube l r))
    (hfib : ∀ z ∈ identityTube l r, ∀ w ∈ identityTube l r,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * l)) = (w.2 : AddCircle (4 * l)))
    (hvalue : ∀ (k : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * l)) (u : Icc (-r) r),
      f ((B k).chart ⟨annulusMap l (by linarith) ((s : AddCircle (4 * l)), u),
        annulus_period_point_mem hr hwidth _ u⟩) = τ (sourceTubeDiagonal k u, s))
    (hpre : ∀ x ∈ squareAnnulus L d,
      f x ∈ τ '' identityTube l r ↔ x ∈ A j ∪ A j.rev) :
    Nonempty (NestedResolvingCylinder (L := L) (d := d) e B j f τ) := by
  obtain ⟨outer, inner, houter, hinner, hOU, hIU, hoend, hiend, hOA, hAO, hAI, hIA,
    hOUA, hIUA, hostrict, histrict⟩ := exists_nested_retained_cylinder_charts
      (B j) (B j.rev) (hA j) (hA j.rev) henclosing hnested hd hsourceWidth
  obtain ⟨a, g, copyO, copyA, copyI, q, haemb, ha, hatube, hg, hcopyO, hcopyA, hcopyI,
    _, hkeepO, hkeepA, hkeepI, _, _, himage, hlevelO, hlowerA, hupperA, hlevelI⟩ :=
    exists_resolving_annulus_with_retained_exteriors_and_levels e hcompat hr hwidth hb hbr
      A (fun k ↦ (B k).chart) (fun k ↦ (B k).chart_PL) j outer inner houter hinner hOU hIU
      hOA hAO hAI hIA f hf τ hτ hfib hvalue
  have hainj : InjOn a (squareAnnulus l r) := by
    intro x hx y hy hxy
    exact congrArg (fun z : squareAnnulus l r ↦ (z : P2))
      (haemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hleft : Left = Set.prod Q (Icc (-1 : ℝ) (-1 / 2)) := by
    congr 2
    ring
  have hmiddle : Middle = Set.prod Q (Icc (-1 / 2 : ℝ) 0) := by
    congr 2
    ring
  let copyO' := copyO.trans (Homeomorph.setCongr hleft)
  let copyA' := copyA.trans (Homeomorph.setCongr hmiddle)
  have hs := resolving_middle_singleton_of_full_tube_preimage outer inner
    copyO' copyA' copyI hOU hIU hpre hOUA hIUA hlevelO hlevelI hainj
      hkeepO hkeepA hkeepI hatube
  have hsingle : ∀ z ∈ Middle, ∀ w ∈ Cyl, g w = g z → w = z := by
    simpa only [← hmiddle] using hs
  exact ⟨{
    outer := outer, inner := inner, outer_PL := houter, inner_PL := hinner
    outer_source := hOU, inner_source := hIU, outer_end := hoend, inner_end := hiend
    outer_strict := hostrict, inner_strict := histrict
    outer_contact := hOUA, inner_contact := hIUA
    annulus := a, map := g, copyO := copyO, copyA := copyA, copyI := copyI
    annulus_embedding := haemb, annulus_PL := ha, annulus_tube := hatube, map_PL := hg
    copyO_PL := hcopyO, copyA_PL := hcopyA, copyI_PL := hcopyI
    keepO := hkeepO, keepA := hkeepA, keepI := hkeepI, image := himage
    copyO_level := hlevelO, copyA_lower := hlowerA, copyA_upper := hupperA
    copyI_level := hlevelI, middle_singleton := hsingle }⟩

namespace NestedResolvingCylinder

variable {e B j} {f : P2 → X} {τ : (P2 × ℝ) → X}

omit [FiniteDimensional ℝ F] [T2Space X] in

theorem boundary_iff (D : NestedResolvingCylinder (L := L) (d := d) e B j f τ)
    (Z : Set X)
    (hf : ∀ x ∈ squareAnnulus L d, f x ∈ Z ↔ depth L x = -d ∨ depth L x = d)
    (hτZ : Disjoint (τ '' identityTube l r) Z) :
    ∀ x : Cyl, D.map x ∈ Z ↔ x.val.2 = -1 ∨ x.val.2 = 1 := by
  obtain ⟨hO, hI⟩ := retained_exterior_boundary_iff f Z hf D.outer_source D.inner_source
    D.outer_strict D.inner_strict D.outer D.inner D.outer_end D.inner_end
  exact resolving_three_piece_boundary_iff D.outer D.inner D.copyO D.copyA D.copyI
    f D.annulus D.map D.keepO D.keepA D.keepI D.copyO_level D.copyI_level hO
      (fun x hx ↦ disjoint_left.mp hτZ (D.annulus_tube ⟨x, x.property, rfl⟩) hx) hI

end NestedResolvingCylinder
end PoincareConjecture.M76.Dehn.Annuli
