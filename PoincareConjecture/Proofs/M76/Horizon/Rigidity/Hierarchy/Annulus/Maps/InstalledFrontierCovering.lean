import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.InstalledBoundaryCoverings

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem isCoveringMap_hamiltonZero_frontier_of_installed_collar
    {E : Type*} [TopologicalSpace E] {K : Set E} {R : Set X0}
    (phi : C(H0, H0)) (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r)
    (c : E × ℝ → X0)
    (hi : IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) ↦ c z))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hvalue : ∀ x : K, (Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1 = g x) :
    IsCoveringMap (hamiltonZeroRetainedTangentialMap phi (frontier R)) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let z : C(K, K ×ˢ Icc (-r) r) :=
    ⟨fun x ↦ ⟨(x, 0), x.property, neg_nonpos.mpr hr, hr⟩, by fun_prop⟩
  let f : C(K, frontier R) := {
    toFun := fun x ↦ ⟨c (x, 0), hzero.subset ⟨(x, 0), ⟨x.property, rfl⟩, rfl⟩⟩
    continuous_toFun := (hi.continuous.comp z.continuous).subtype_mk _ }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hz : z x = z y := hi.injective (congrArg Subtype.val hxy)
      exact Subtype.ext (congrArg (fun w : K ×ˢ Icc (-r) r ↦ w.val.1) hz)
    · intro y
      obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, hxy⟩ := hzero.symm.subset y.property
      have ht0 : t = 0 := ht
      subst t
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let H : K ≃ₜ frontier R :=
    (Equiv.ofBijective f hf).toHomeomorphOfContinuousClosed f.continuous f.continuous.isClosedMap
  have heq : (hamiltonZeroRetainedTangentialMap phi (frontier R) :
      frontier R → C0 × C0) = g ∘ H.symm := by
    funext y
    obtain ⟨x, rfl⟩ := H.surjective y
    rw [Function.comp_apply, H.symm_apply_apply]
    exact hvalue x
  rw [heq]
  exact hg.comp_homeomorph H.symm

end PoincareConjecture.M76
