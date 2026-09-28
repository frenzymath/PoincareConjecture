import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.SquareTwoIntervalNormalization
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition










set_option autoImplicit false

open Set Metric Geometry
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1



theorem exists_two_interval_disk_normalization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S U V : Set E} {a b : E} (hS : IsFinitePLBallPair (ℝ × ℝ) S (U ∪ V))
    (hab : a ≠ b) (hUV : U ∩ V = {a, b})
    (p0 : I01 ≃ₜ U) (p1 : I01 ≃ₜ V)
    (hp0 : p0.IsFinitePL) (hp1 : p1.IsFinitePL)
    (hp00 : (p0 (0 : unitInterval) : E) = a)
    (hp01 : (p0 (1 : unitInterval) : E) = b)
    (hp10 : (p1 (0 : unitInterval) : E) = a)
    (hp11 : (p1 (1 : unitInterval) : E) = b) :
    ∃ (H : Q ≃ₜ (U ∪ V : Set E)) (d : V2 → E),
      H.IsFinitePL ∧ FinitePiecewiseAffineOn d D ∧
      Topology.IsEmbedding (fun x : D => d x) ∧ d '' D = S ∧
      (∀ x : Q, d x = (H x : E)) ∧
      (∀ x : D, d x ∈ U ∪ V ↔ (x : V2) ∈ Q) ∧
      (∀ t : I01, d (squareRimLoop (squareRimHalfTime false t)) = p0 t) ∧
      (∀ t : I01, d (squareRimLoop (squareRimHalfTime true t)) = p1 t) ∧
      ∃ hbase : (H squareRimBase : E) = a,
        ((squareRimLoop.map (continuous_subtype_val.comp H.continuous)).cast
          hbase.symm hbase.symm) =
          ((intervalChartPath p0).cast hp00.symm hp01.symm).trans
            ((intervalChartPath p1).cast hp10.symm hp11.symm).symm := by
  obtain ⟨H, hH, h0, h1, hbase, hloop⟩ :=
    exists_squareRim_two_interval_normalization hab hUV p0 p1 hp0 hp1 hp00 hp01 hp10 hp11
  obtain ⟨G, hG, hrim, hiff⟩ :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).exists_extension hS H hH
  obtain ⟨d, hd, hval⟩ := hG
  have hemb : Topology.IsEmbedding (fun x : D => d x) := by
    have heq : (fun x : D => d x) = fun x : D => (G x : E) := funext fun x => (hval x).symm
    rw [heq]
    exact Topology.IsEmbedding.subtypeVal.comp G.isEmbedding
  have himage : d '' D = S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hval ⟨x, hx⟩ ▸ (G ⟨x, hx⟩).property
    · intro hy
      refine ⟨G.symm ⟨y, hy⟩, (G.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hval, G.apply_symm_apply]
  have hdH (x : Q) : d x = (H x : E) := by
    have h := congrArg Subtype.val (hrim x)
    rwa [hval] at h
  refine ⟨H, d, hH, hd, hemb, himage, hdH, ?_, ?_, ?_, hbase, hloop⟩
  · intro x
    have h := hiff x
    rw [hval] at h
    exact h.symm
  · intro t
    exact (hdH _).trans (h0 t)
  · intro t
    exact (hdH _).trans (h1 t)



theorem polyhedralPL_square_normalization
    {E F X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    {S : Set E} {f : E → X} (hf : PolyhedralPLInCharts e f S)
    {d : V2 → E} (hd : FinitePiecewiseAffineOn d D) (himage : d '' D = S) :
    PolyhedralPLInCharts e (f ∘ d) D ∧ (f ∘ d) '' D = f '' S := by
  have hcopy := hd
  obtain ⟨K, hK, hKs, _⟩ := hcopy
  have hdK : FinitePiecewiseAffineOn d K.space := by simpa only [hKs] using hd
  have hmaps : MapsTo d K.space S := fun x hx => himage.subset ⟨x, hKs.subset hx, rfl⟩
  refine ⟨?_, ?_⟩
  · simpa only [hKs] using hf.comp_finitePiecewiseAffineOn K hK hdK hmaps
  · rw [image_comp, himage]

end PoincareConjecture.M76.Dehn
