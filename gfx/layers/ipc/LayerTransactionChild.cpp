/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 2 -*-
 * vim: sw=2 ts=8 et :
 */
/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "LayerTransactionChild.h"
#include "mozilla/layers/CompositableClient.h"  // for CompositableChild
#include "mozilla/layers/LayersSurfaces.h"  // for PGrallocBufferChild
#include "mozilla/layers/PCompositableChild.h"  // for PCompositableChild
#include "mozilla/layers/PLayerChild.h"  // for PLayerChild
#include "mozilla/layers/ShadowLayers.h"  // for ShadowLayerForwarder
#include "mozilla/mozalloc.h"           // for operator delete, etc
#include "nsDebug.h"                    // for NS_RUNTIMEABORT, etc
#include "nsTArray.h"                   // for nsTArray
#include "mozilla/layers/TextureClient.h"

namespace mozilla {
namespace layers {

class PGrallocBufferChild;

void
LayerTransactionChild::Destroy()
{
  if (!IPCOpen() || mDestroyed) {
    return;
  }
  // mDestroyed is used to prevent calling Send__delete__() twice.
  // When this function is called from CompositorChild::Destroy(),
  // under Send__delete__() call, this function is called from
  // ShadowLayerForwarder's destructor.
  // When it happens, IPCOpen() is still true.
  // See bug 1004191.
  mDestroyed = true;
  NS_ABORT_IF_FALSE(0 == ManagedPLayerChild().Length(),
                    "layers should have been cleaned up by now");
  PLayerTransactionChild::Send__delete__(this);
}

PGrallocBufferChild*
LayerTransactionChild::AllocPGrallocBufferChild(const IntSize&,
                                                const uint32_t&,
                                                const uint32_t&,
                                                MaybeMagicGrallocBufferHandle*)
{
#ifdef MOZ_HAVE_SURFACEDESCRIPTORGRALLOC
  return GrallocBufferActor::Create();
#else
  NS_RUNTIMEABORT("No gralloc buffers for you");
  return nullptr;
#endif
}

bool
LayerTransactionChild::DeallocPGrallocBufferChild(PGrallocBufferChild* actor)
{
#ifdef MOZ_HAVE_SURFACEDESCRIPTORGRALLOC
  delete actor;
  return true;
#else
  NS_RUNTIMEABORT("Um, how did we get here?");
  return false;
#endif
}

PLayerChild*
LayerTransactionChild::AllocPLayerChild()
{
  // we always use the "power-user" ctor
  NS_RUNTIMEABORT("not reached");
  return nullptr;
}

bool
LayerTransactionChild::DeallocPLayerChild(PLayerChild* actor)
{
  delete actor;
  return true;
}

PCompositableChild*
LayerTransactionChild::AllocPCompositableChild(const TextureInfo& aInfo)
{
  return new CompositableChild();
}

bool
LayerTransactionChild::DeallocPCompositableChild(PCompositableChild* actor)
{
  delete actor;
  return true;
}

bool
LayerTransactionChild::RecvParentAsyncMessage(const InfallibleTArray<AsyncParentMessageData>& aMessages)
{
  for (AsyncParentMessageArray::index_type i = 0; i < aMessages.Length(); ++i) {
    const AsyncParentMessageData& message = aMessages[i];

    switch (message.type()) {
      case AsyncParentMessageData::TOpDeliverFence: {
        const OpDeliverFence& op = message.get_OpDeliverFence();
        FenceHandle fence = op.fence();
        PTextureChild* child = op.textureChild();

        RefPtr<TextureClient> texture = TextureClient::AsTextureClient(child);
        if (texture) {
          texture->SetReleaseFenceHandle(fence);
        }
        if (mForwarder) {
          mForwarder->HoldTransactionsToRespond(op.transactionId());
        } else {
          // Send back a response.
          InfallibleTArray<AsyncChildMessageData> replies;
          replies.AppendElement(OpReplyDeliverFence(op.transactionId()));
          SendChildAsyncMessages(replies);
        }
        break;
      }
      default:
        NS_ERROR("unknown AsyncParentMessageData type");
        return false;
    }
  }
  return true;
}

void
LayerTransactionChild::ActorDestroy(ActorDestroyReason why)
{
#ifdef MOZ_B2G
  // Due to poor lifetime management of gralloc (and possibly shmems) we will
  // crash at some point in the future when we get destroyed due to abnormal
  // shutdown. Its better just to crash here. On desktop though, we have a chance
  // of recovering.
  if (why == AbnormalShutdown) {
    NS_RUNTIMEABORT("ActorDestroy by IPC channel failure at LayerTransactionChild");
  }
#endif
}

PTextureChild*
LayerTransactionChild::AllocPTextureChild(const SurfaceDescriptor&,
                                          const TextureFlags&)
{
  return TextureClient::CreateIPDLActor();
}

bool
LayerTransactionChild::DeallocPTextureChild(PTextureChild* actor)
{
  return TextureClient::DestroyIPDLActor(actor);
}

}  // namespace layers
}  // namespace mozilla
