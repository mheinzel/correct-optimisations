module Transformations where

import Language.Core
import Language.DeBruijn
import Language.CoDeBruijn
import Language.Generic
import Language.Generic.DeBruijn
import Language.Generic.CoDeBruijn

import Transformations.Recursion

import Transformations.DeBruijn.Live
import Transformations.DeBruijn.StronglyLive
import Transformations.DeBruijn.DeadBindingDirect
import Transformations.DeBruijn.DeadBindingEfficient  -- TODO: rename to DeadBindingLive
import Transformations.DeBruijn.DeadBindingStrong  -- TODO: rename to DeadBindingStronglyLive
import Transformations.DeBruijn.LetInward

import Transformations.CoDeBruijn.DeadBinding
import Transformations.CoDeBruijn.DeadBindingStrong
import Transformations.CoDeBruijn.LetInward

import Transformations.Generic.CoDeBruijn.DeadBinding
import Transformations.Generic.CoDeBruijn.DeadBindingStrong
