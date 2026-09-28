import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.C1HomotopyLifting
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.NullLoopHomotopy
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.RawRegularization
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Topology.Metrizable.Uniformity









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M]



theorem m59_c1_path_of_null_loop
    (hcompact : IsCompact (univ : Set M)) (gamma : C1FreeLoopSpace (M := M))
    (hgamma : IsNullHomotopicLoop gamma) :
    ∃ p : M, Nonempty (Path gamma (constantC1Loop p)) := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 3) M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨f, hf, hb⟩ := hgamma
  let F : C((Fin 0 → I), C1FreeLoopSpace (M := M)) := ContinuousMap.const _ gamma
  let G : C((Fin 0 → I), C1FreeLoopSpace (M := M)) := ContinuousMap.const _ (constantC1Loop (f 0))
  let H : C(I × ((Fin 0 → I) × LoopCircle), M) :=
    ⟨fun q => f ((1 - (q.1 : ℝ)) • q.2.2.val), hf.comp
      ((continuous_const.sub continuous_fst.subtype_val).smul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))⟩
  have h0 (v : Fin 0 → I) (z : LoopCircle) : H (0, (v, z)) = F v z := by
    change f ((1 - (0 : ℝ)) • z.val) = gamma z
    simpa only [sub_zero, one_smul] using hb z
  have h1 (v : Fin 0 → I) (z : LoopCircle) : H (1, (v, z)) = G v z := by
    change f ((1 - (1 : ℝ)) • z.val) = f 0
    rw [sub_self, zero_smul]
  obtain ⟨K, _⟩ := m59_c1_homotopy_of_value_homotopy hcompact 0 (f 0) F G H h0 h1
  let v : Fin 0 → I := Fin.elim0
  exact ⟨f 0, ⟨{
    toFun := fun t => K (t, v)
    continuous_toFun := K.continuous.comp (continuous_id.prodMk continuous_const)
    source' := K.apply_zero v
    target' := K.apply_one v }⟩⟩



theorem m59_inIdentityComponent_of_null_loop
    (hcompact : IsCompact (univ : Set M)) (hconnected : IsConnected (univ : Set M))
    (x : M) (gamma : C1FreeLoopSpace (M := M)) (hgamma : IsNullHomotopicLoop gamma) :
    InIdentityComponent x gamma := by
  let : ConnectedSpace M := connectedSpace_iff_univ.mpr hconnected
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace LoopAmbient M
  let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨p, ⟨P⟩⟩ := m59_c1_path_of_null_loop hcompact gamma hgamma
  let Q := (PathConnectedSpace.somePath p x).map Proofs.M58.continuous_constantC1Loop
  let R := P.trans Q
  exact ⟨R, R.continuous, R.source, R.target⟩



theorem m59_identity_component
    (hcompact : IsCompact (univ : Set M)) (hconnected : IsConnected (univ : Set M))
    (x : M) (gamma : C1FreeLoopSpace (M := M)) :
    InIdentityComponent x gamma ↔ IsNullHomotopicLoop gamma :=
  ⟨m59NullLoop_of_inIdentityComponent x gamma,
    m59_inIdentityComponent_of_null_loop hcompact hconnected x gamma⟩



theorem m59_raw_regularization
    (hcompact : IsCompact (univ : Set M)) (hconnected : IsConnected (univ : Set M))
    (q : M59SphereQuotient) (x : M)
    (F : C(LoopTwoSphere, C1FreeLoopSpace (M := M)))
    (hF : ∀ c, IsNullHomotopicLoop (F c)) :
    ∃ Gamma : FreeTwoSphereFamily (M := M),
      M59NormalizedAt q x Gamma ∧ F.Homotopic (m59FamilyMap Gamma) := by
  obtain ⟨P, hP, h0, h1⟩ :=
    m59_inIdentityComponent_of_null_loop hcompact hconnected x (F q.pole) (hF q.pole)
  exact m59_raw_regularization_of_pole_path q x F ⟨⟨P, hP⟩, h0, h1⟩

end PoincareConjecture
