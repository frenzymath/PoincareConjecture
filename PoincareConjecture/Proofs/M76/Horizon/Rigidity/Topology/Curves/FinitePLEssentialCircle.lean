import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.EssentialAnnulusCircle
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimPolygon
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneSquareCircle










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Geometry PLAnnularStrip unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1


noncomputable def annulusCoreCircle : C(Circle, Ann) :=
  ⟨fun z => annulusCylinderHomeomorph (⟨1 / 2, by norm_num⟩, z),
    annulusCylinderHomeomorph.continuous.comp (continuous_const.prodMk continuous_id)⟩

theorem annulusCoreCircle_apply (z : Circle) :
    (annulusCoreCircle z : P2) = annulusMap 8 (by norm_num) (z, 0) := by
  rw [annulusCoreCircle, ContinuousMap.coe_mk, annulusCylinderHomeomorph_apply]
  change annulusMap 8 (by norm_num) (z, 2 * (1 / 2 : ℝ) - 1) = _
  norm_num



theorem exists_polygon_of_finitePL_embedded_square_rim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (gamma : C(Q2, E)) (hinj : Function.Injective gamma)
    (f : V2 → E) (hf : FinitePiecewiseAffineOn f Q2)
    (hvalue : ∀ x : Q2, f x = gamma x) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)), P.HasSimplicialEdges ∧
      Function.Injective P ∧ P.boundary ℝ = range gamma := by
  have hfi : InjOn f Q2 := by
    intro x hx y hy hxy
    have heq : gamma ⟨x, hx⟩ = gamma ⟨y, hy⟩ :=
      (hvalue ⟨x, hx⟩).symm.trans (hxy.trans (hvalue ⟨y, hy⟩))
    exact congrArg Subtype.val (hinj heq)
  obtain ⟨n, P, hPi, hP, hPb⟩ := squareRimPolygon.exists_polygon_finitePL_image
    hasSimplicialEdges_squareRimPolygon injective_squareRimPolygon hf
    (by rw [boundary_squareRimPolygon])
    (by simpa only [boundary_squareRimPolygon] using hfi)
  rw [boundary_squareRimPolygon] at hPb
  refine ⟨n, P, hP, hPi, hPb.trans ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (hvalue ⟨x, hx⟩).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, hvalue x⟩



noncomputable def annulusOuterRimToCore :
    (⟨annulusRimPoint false, continuous_annulusRimPoint false⟩ :
      C(Circle, Ann)).Homotopy annulusCoreCircle where
  toFun z := annulusCylinderHomeomorph
    (⟨(z.1 : ℝ) / 2, by constructor <;> linarith [z.1.property.1, z.1.property.2]⟩, z.2)
  continuous_toFun := annulusCylinderHomeomorph.continuous.comp
    ((Continuous.subtype_mk (by fun_prop)
      (fun z => by constructor <;> linarith [z.1.property.1, z.1.property.2])).prodMk
        continuous_snd)
  map_zero_left z := by
    change annulusCylinderHomeomorph (⟨(0 : ℝ) / 2, _⟩, z) = annulusRimPoint false z
    exact (congrArg (fun t : I => annulusCylinderHomeomorph (t, z))
      (show (⟨(0 : ℝ) / 2, _⟩ : I) = 0 from Subtype.ext (by norm_num))).trans
      (annulusCylinderHomeomorph_zero z)
  map_one_left z := rfl





theorem exists_finitePL_essential_annulus_core_homotopy
    (gamma : C(Q2, Ann)) (hinj : Function.Injective gamma)
    (f : V2 → P2) (hf : FinitePiecewiseAffineOn f Q2)
    (hvalue : ∀ x : Q2, f x = (gamma x : P2))
    (hdepth : ∀ x : Q2, -1 < depth 8 (gamma x : P2) ∧ depth 8 (gamma x : P2) < 1)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1) :
    ∃ q : Q2 ≃ₜ Circle,
      Nonempty (gamma.Homotopy
        (annulusCoreCircle.comp ⟨q, q.continuous⟩)) := by
  let ambient : C(Q2, P2) := ⟨fun x => gamma x, continuous_subtype_val.comp gamma.continuous⟩
  have hai : Function.Injective ambient := by
    intro x y h
    exact hinj (Subtype.ext h)
  obtain ⟨n, P, hP, hi, hPb⟩ :=
    exists_polygon_of_finitePL_embedded_square_rim ambient hai f hf hvalue
  have hboundary : ∀ p ∈ P.boundary ℝ, -1 < depth 8 p ∧ depth 8 p < 1 := by
    intro p hp
    obtain ⟨x, rfl⟩ := hPb.subset hp
    exact hdepth x
  have hgamma : ∀ x, (gamma x : P2) ∈ P.boundary ℝ := fun x =>
    hPb.symm.subset (mem_range_self x)
  let J : Circle ≃ₜ Q2 :=
    (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (2 : ℝ))
      (by norm_num) (by norm_num)).trans HamiltonIndexOne.squareCircle
  let j : C(Circle, Ann) := gamma.comp ⟨J, J.continuous⟩
  have hji : Function.Injective j := hinj.comp J.injective
  have hj : range (fun z => (j z : P2)) = P.boundary ℝ := by
    rw [hPb]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨J z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨J.symm z, by simp only [j, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk, J.apply_symm_apply]; rfl⟩
  obtain ⟨q, ⟨H⟩⟩ := exists_essential_polygon_rim_homotopy P hP hi hboundary
    gamma hgamma hessential j hji hj
  let Hcore : (⟨fun z => annulusRimPoint false (q z),
      (continuous_annulusRimPoint false).comp q.continuous⟩ : C(Circle, Ann)).Homotopy
      (annulusCoreCircle.comp ⟨q, q.continuous⟩) := {
    toFun := fun z => annulusOuterRimToCore (z.1, q z.2)
    continuous_toFun := annulusOuterRimToCore.continuous.comp
      (continuous_fst.prodMk (q.continuous.comp continuous_snd))
    map_zero_left := fun z => annulusOuterRimToCore.apply_zero (q z)
    map_one_left := fun z => annulusOuterRimToCore.apply_one (q z) }
  let G := H.trans Hcore
  refine ⟨J.symm.trans q, ⟨{
    toFun := fun z => G (z.1, J.symm z.2)
    continuous_toFun := G.continuous.comp
      (continuous_fst.prodMk (J.symm.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := fun z => G.apply_one (J.symm z)
  }⟩⟩
  intro z
  rw [G.apply_zero]
  exact congrArg gamma (J.apply_symm_apply z)

end PoincareConjecture.M76.Dehn
