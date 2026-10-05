import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.RadialRescalingHomeomorph
import Mathlib.Topology.Homotopy.Basic

/-!
# A continuous PL deformation for radial vertex rescaling

Linear interpolation between the identity and a positive radial vertex
map stays an embedding of the carrier at every time. Joint continuity
uses one explicit interpolation formula. See Cairns 1940, Lemma 5.3,
pp. 801--802 and M76 derivation 17. This treats a fixed embedded complex;
dependence on varying original embeddings is a separate assertion.
-/

set_option autoImplicit false

open Set NormedSpace
open scoped unitInterval

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f g : E → F}

/-- Interpolation of two face-affine maps remains affine on each face.
See the vertex deformation in Cairns p. 801 and M76 derivation 17. -/
theorem AffineOnFaces.interpolate (hf : K.AffineOnFaces f) (hg : K.AffineOnFaces g) (t : ℝ) :
    K.AffineOnFaces (fun x => (1 - t) • f x + t • g x) := by
  intro s hs
  obtain ⟨a, ha⟩ := hf s hs
  obtain ⟨b, hb⟩ := hg s hs
  refine ⟨(1 - t) • a + t • b, fun x hx => ?_⟩
  simp only [ContinuousAffineMap.add_apply, ContinuousAffineMap.smul_apply, ha hx, hb hx]

/-- Interpolation of the positive numbers one and r stays positive
throughout the closed unit interval. See Cairns p. 801 and M76 derivation 17. -/
theorem radial_interpolation_pos {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 - t + t * r := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · simp [← h]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (mul_pos h hr)

variable [DecidableEq E] [FiniteDimensional ℝ E] {f : E → E}

/-- At each time, the explicit interpolation is the homeomorphism
onto the complex with interpolated vertex radii. The inverse remains
affine on every target face. See Cairns Lemma 5.3 and M76 derivation 17. -/
theorem exists_radial_interpolation_homeomorph
    (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x)
    (hf : K.AffineOnFaces f) (hfv : EqOn f (fun x => r x • x) K.vertices)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ (g : E → E)
      (e : K.space ≃ₜ
        (K.radialRescale hlin hinj (fun x => 1 - t + t * r x)
          (fun x hx => radial_interpolation_pos (hr x hx) ht)).space),
      (K.radialRescale hlin hinj (fun x => 1 - t + t * r x)
        (fun x hx => radial_interpolation_pos (hr x hx) ht)).AffineOnFaces g ∧
      (∀ x : K.space, (e x : E) = (1 - t) • (x : E) + t • f x) ∧
      (∀ y, (e.symm y : E) = g y) := by
  obtain ⟨F, g, e, hF, hg, hFv, heF, heg⟩ :=
    K.exists_radialRescale_homeomorph hK hlin hinj (fun x => 1 - t + t * r x)
      (fun x hx => radial_interpolation_pos (hr x hx) ht)
  have hinterp := (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)).interpolate hf t
  have heq : EqOn F (fun x => (1 - t) • x + t • f x) K.space :=
    hF.eqOn_of_eqOn_vertices hinterp (fun x hx => by
      simp only [hFv hx, hfv hx, add_smul, mul_smul])
  exact ⟨g, e, hg, fun x => (heF x).trans (heq x.property), heg⟩

/-- The explicit radial vertex interpolation is a homotopy through
embeddings affine on the fixed source faces. See Cairns Lemma 5.3,
pp. 801--802 and M76 derivation 17. -/
noncomputable def radialRescaleHomotopy
    (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x)
    (hf : K.AffineOnFaces f) (hfv : EqOn f (fun x => r x • x) K.vertices) :
    ContinuousMap.HomotopyWith
      (⟨Subtype.val, continuous_subtype_val⟩ : C(K.space, E))
      ⟨fun x => f x, (hf.continuousOn hK).domRestrict⟩
      (fun F => Topology.IsEmbedding F ∧
        ∃ g : E → E, K.AffineOnFaces g ∧ ∀ x : K.space, g x = F x) where
  toFun tx := (1 - (tx.1 : ℝ)) • (tx.2 : E) + (tx.1 : ℝ) • f tx.2
  continuous_toFun := by
    have ht : Continuous (fun tx : I × K.space => (tx.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun tx : I × K.space => (tx.2 : E)) :=
      continuous_subtype_val.comp continuous_snd
    have hfx : Continuous (fun tx : I × K.space => f tx.2) :=
      (hf.continuousOn hK).domRestrict.comp continuous_snd
    exact ((continuous_const.sub ht).smul hx).add (ht.smul hfx)
  map_zero_left x := by simp
  map_one_left x := by
    change (1 - (1 : ℝ)) • (x : E) + (1 : ℝ) • f x = f x
    simp
  prop' t := by
    obtain ⟨g, e, _, he, _⟩ :=
      exists_radial_interpolation_homeomorph hK hlin hinj r hr hf hfv t.property
    refine ⟨?_, fun x => (1 - (t : ℝ)) • x + (t : ℝ) • f x,
      (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)).interpolate hf t, fun _ => rfl⟩
    have h := (Topology.IsEmbedding.subtypeVal).comp e.isEmbedding
    convert h using 1
    ext x
    exact (he x).symm

/-- A vertex whose target radius is unchanged is fixed for the whole
radial interpolation. See Cairns p. 801 and M76 derivation 17. -/
theorem radialRescaleHomotopy_fixed_vertex
    (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x)
    (hf : K.AffineOnFaces f) (hfv : EqOn f (fun x => r x • x) K.vertices)
    {x : E} (hx : x ∈ K.vertices) (hxr : r x = 1) (t : I) :
    radialRescaleHomotopy hK hlin hinj r hr hf hfv (t, ⟨x, vertices_subset_space hx⟩) = x := by
  change (1 - (t : ℝ)) • x + (t : ℝ) • f x = x
  simp only [hfv hx, hxr, one_smul]
  rw [← add_smul]
  simp

end Geometry.SimplicialComplex
