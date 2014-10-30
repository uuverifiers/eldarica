/**
 * Copyright (c) 2011-2014 Philipp Ruemmer. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


package lazabs;

import ap.util.CmdlParser

import scala.collection.mutable.ArrayBuffer
import scala.actors.Actor._
import scala.actors.{Actor, TIMEOUT}

import java.net._

object ServerMain {

  private val InactivityTimeout = 60 * 60 * 1000 // shutdown after 15min inactivity
  private val TicketLength = 40
  private val MaxThreadNum = 2
  private val MaxWaitNum   = 32

  private case class ThreadToken(stopTime : Long)

  //////////////////////////////////////////////////////////////////////////////

  def main(args : Array[String]) : Unit = {

    // since some of the actors in the class use blocking file operations,
    // we have to disable the actor-fork-join stuff to prevent deadlocks
    sys.props += ("actors.enableForkJoin" -> "false")

    val predefPort = args match {
      case Array(CmdlParser.IntVal(v)) => Some(v)
      case _ => None
    }

    val socket =
      new ServerSocket(predefPort getOrElse 0, MaxWaitNum,
                       InetAddress getByName "localhost")
    val port = socket.getLocalPort

    socket.setSoTimeout(InactivityTimeout / 2)

    Console.withOut(Console.err) {
      println(lazabs.Main.greeting)
      println
      println("Daemon started on port " + port)
    }

    val r = new scala.util.Random
    val ticket =
      (for (_ <- 0 until TicketLength) yield r.nextPrintableChar) mkString ""

    println(port)
    println(ticket)

    val serverActor = self
    for (_ <- 0 until MaxThreadNum)
      serverActor ! ThreadToken(System.currentTimeMillis)

    ////////////////////////////////////////////////////////////////////////////
    // The main loop

    var serverRunning = true
    while (serverRunning) {

      // Get a token to serve another request
      val curToken = receive {
        case t : ThreadToken => t
      }

      try {
        val clientSocket = socket.accept

        actor {
          Console setErr lazabs.horn.bottomup.HornWrapper.NullStream
  
          val inputReader =
            new java.io.BufferedReader(
            new java.io.InputStreamReader(clientSocket.getInputStream))
    
          val receivedTicket = inputReader.readLine
          if (ticket == receivedTicket) {
            val arguments = new ArrayBuffer[String]
    
            var str = inputReader.readLine
            var done = false
            while (!done && str != null) {
              str.trim match {
                case "PROVE_AND_EXIT" => {
                  done = true
                  Console.withOut(clientSocket.getOutputStream) {
                    var checkNum = 0
                    var lastPing = System.currentTimeMillis
                    var cancel = false
  
                    try {
                      Main.doMain(arguments.toArray, {
                        checkNum = checkNum + 1
                        cancel || {
                          val currentTime = System.currentTimeMillis
                          while (inputReader.ready) {
                            inputReader.read
                            lastPing = currentTime
                          }
                          cancel = currentTime - lastPing > 3000
                          cancel
                        }
                      })
                    } catch {
                      case t : StackOverflowError => {
                        System.gc
                        // let's hope that everything is still in a valid state
                        println("ERROR: " + t)
                      }
                      case t : OutOfMemoryError => {
                        System.gc
                        // let's hope that everything is still in a valid state
                        println("ERROR: " + t)
                      }
                      case t : Throwable =>
                        println("ERROR: " + t)
                    }
                  }
                }
                case str =>
                  arguments += str
              }
    
              if (!done)
                str = inputReader.readLine
            }
          }
    
          inputReader.close
  
          // Put back the token
          serverActor ! ThreadToken(System.currentTimeMillis)
        }
  
      } catch {
        case _ : SocketTimeoutException => {
          // check whether any other thread is still active
  
          serverActor ! curToken

          var joinedThreads = List[ThreadToken]()
          var stillActive = false
          while (!stillActive && joinedThreads.size < MaxThreadNum)
            receiveWithin(0) {
              case t : ThreadToken => {
                joinedThreads = t :: joinedThreads
                // some thread only finished recently
                stillActive =
                  System.currentTimeMillis - t.stopTime < InactivityTimeout
              }
              case TIMEOUT => {
                // there are still some threads running
                stillActive = true
              }
            }
  
          if (stillActive) {
            for (t <- joinedThreads)
              serverActor ! t
          } else {
            Console.err.println("Shutting down inactive Eldarica daemon")
            serverRunning = false
          }
        }
      }
    }
  }
}
