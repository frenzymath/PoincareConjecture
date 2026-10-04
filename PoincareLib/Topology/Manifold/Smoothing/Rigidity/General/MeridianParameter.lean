import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Levels.MeridianCut
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.PolyhedralPLDiskExtension

/-!
# Literal meridian parameters in the original domain subtype

The parameter map retains every original disk and circle value
on the whole cylinder. Its period identity and supplied-atlas
PL certificates hold on complete finite boxes. See derivation 010.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

/-- A total representative of the original quotient parameter.
Only values on the full disk cylinder occur in later certificates.
See rigidity derivation 010. -/
noncomputable def hamiltonMeridianParameter (z : E) : R := by
  classical
  refine ⟨(if z.1 ∈ D then z.1 else 0,
    QuotientAddGroup.mk (fun _ : Fin 1 => z.2)), ?_, mem_univ _⟩
  split_ifs with h
  · exact h
  · exact mem_closedBall_self zero_le_one

/-- Every original disk parameter retains its exact ambient
quotient value, at every real time. See derivation 010. -/
theorem hamiltonMeridianParameter_val (z : E) (hz : z.1 ∈ D) :
    (hamiltonMeridianParameter z : X) = hamiltonMeridianCutAmbientMap z := by
  simp only [hamiltonMeridianParameter, if_pos hz, hamiltonMeridianCutAmbientMap]

/-- The same original product-subtype identification gives the
already constructed total cut map. See derivation 010. -/
theorem hamiltonMeridianParameter_domainEquiv (x : D) (t : ℝ) :
    latticeHandleDomainEquiv (Fin 2) (Fin 1) L (hamiltonMeridianParameter (x, t)) =
      hamiltonMeridianCutMap (x, t) := by
  classical
  rw [hamiltonMeridianCutMap_apply]
  apply Prod.ext
  · apply Subtype.ext
    change (if (x : V2) ∈ D then (x : V2) else 0) = x
    exact if_pos x.property
  · rfl

/-- The full original cylinder has the actual continuous
quotient formula, including the whole disk rim. See derivation 010. -/
theorem continuousOn_hamiltonMeridianParameter :
    ContinuousOn hamiltonMeridianParameter (D ×ˢ (univ : Set ℝ)) := by
  have hc : Continuous hamiltonMeridianCutAmbientMap :=
    continuous_fst.prodMk (QuotientAddGroup.continuous_mk.comp
      (continuous_pi fun _ : Fin 1 => continuous_snd))
  exact Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
    (hc.continuousOn.congr (fun z hz => hamiltonMeridianParameter_val z hz.1))

/-- The exact original period identifies every full transverse
disk, with no boundary-only restriction. See derivation 010. -/
theorem hamiltonMeridianParameter_period (x : V2) (t : ℝ) :
    hamiltonMeridianParameter (x, t + p) = hamiltonMeridianParameter (x, t) := by
  classical
  apply Subtype.ext
  change (if x ∈ D then x else 0,
    QuotientAddGroup.mk (fun _ : Fin 1 => t + p)) =
      (if x ∈ D then x else 0, QuotientAddGroup.mk (fun _ : Fin 1 => t))
  apply Prod.ext
  · rfl
  · change QuotientAddGroup.mk (fun _ : Fin 1 => t + p) =
      QuotientAddGroup.mk (fun _ : Fin 1 => t)
    apply hamiltonSolidTorusCircleEquiv.injective
    rw [hamiltonSolidTorusCircleEquiv_mk, hamiltonSolidTorusCircleEquiv_mk,
      AddCircle.coe_add, AddCircle.coe_period, add_zero]

/-- Every whole closed disk box has an exact finite carrier.
See rigidity derivation 010. -/
theorem exists_finite_hamiltonMeridianBox {a b : ℝ} (hab : a < b) :
    ∃ K : SimplicialComplex ℝ E,
      K.faces.Finite ∧ K.space = D ×ˢ Icc a b := by
  obtain ⟨_, _, _, _, _, e, he, _⟩ :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod (isFinitePLBallPair_Icc hab)
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := he
  exact ⟨K, hK, hKs⟩

/-- The supplied standard atlas certifies the original quotient
parameter on every complete finite box. See derivation 010. -/
theorem StandardLatticeHandleAtlas.polyhedralPL_meridianParameter
    {β : Type*} {d : β → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    {a b : ℝ} (hab : a < b) :
    PolyhedralPLInCharts d (fun z => (hamiltonMeridianParameter z : X))
      (D ×ˢ Icc a b) := by
  obtain ⟨K, hK, hKbox⟩ := exists_finite_hamiltonMeridianBox hab
  let A : E →ᴬ[ℝ] ((Fin 2 ⊕ Fin 1) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 2) (Fin 1)
      (fun _ => ℝ)).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
        ((ContinuousLinearMap.fst ℝ V2 ℝ).prod
          (ContinuousLinearMap.pi fun _ : Fin 1 =>
            ContinuousLinearMap.snd ℝ V2 ℝ)).toContinuousAffineMap
  have hA : FinitePiecewiseAffineOn A (D ×ˢ Icc a b) :=
    ⟨K, hK, hKbox, K.affineOnFaces_affine A⟩
  have hcut : PolyhedralPLInCharts d hamiltonMeridianCutAmbientMap (D ×ˢ Icc a b) :=
    hd.polyhedralPL_projection hA
  exact hcut.congr (fun z hz => (hamiltonMeridianParameter_val z hz.1).symm)

end PoincareMT.M76
