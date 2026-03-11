/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderInstaller.lean

  Historical public installer for `XiAtOrderCoords01Provider`.

  UPDATED POLICY:
  This file is now only a compatibility import surface.
  The actual provider is installed theorem-side from:
    * the sigma provider theorem surface
    * the true-analytic Row012 convolution corridor
    * XiSigma3Nonzero

  This removes the fallback coords01 axiom installer from the main live cone.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderInstallerFromSigmaAndRow012TrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticAdapterFromUpstream
import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticFromUpstream
import Hyperlocal.Targets.XiPacket.XiSigma3Nonzero

set_option autoImplicit false
noncomputable section
