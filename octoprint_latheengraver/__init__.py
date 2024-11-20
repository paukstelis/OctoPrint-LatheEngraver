#!/usr/bin/python
# -*- coding: utf-8 -*-
#
# Written by:  Shell M. Shrader (https://github.com/synman/Octoprint-Bettergrblsupport)
# Copyright [2021] [Shell M. Shrader]
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# References
#
# https://web.archive.org/web/20211123161339/https://wiki.shapeoko.com/index.php/G-Code
# https://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=B69BCE8C0F7F5071B56B464AB4CA8C56?doi=10.1.1.15.7813&rep=rep1&type=pdf
# https://github.com/gnea/grbl/blob/master/doc/markdown/commands.md
# https://github.com/gnea/grbl/wiki/Grbl-v1.1-Jogging
# https://github.com/gnea/grbl/wiki/Grbl-v1.1-Configuration#10---status-report-mask
# https://github.com/gnea/grbl/wiki/Grbl-v1.1-Interface#grbl-push-messages
# https://reprap.org/wiki/G-code
#
from __future__ import absolute_import
from pydoc import Helper
from octoprint.events import Events
from shutil import copyfile

from . import _bgs

import octoprint.plugin

import sys
import os
import time
import subprocess
import threading

import re
import logging
import json
import flask
import yaml
import math
import requests

class LatheEngraverPlugin(octoprint.plugin.SettingsPlugin,
                              octoprint.plugin.SimpleApiPlugin,
                              octoprint.plugin.AssetPlugin,
                              octoprint.plugin.TemplatePlugin,
                              octoprint.plugin.StartupPlugin,
                              octoprint.plugin.EventHandlerPlugin,
                              octoprint.plugin.WizardPlugin,
                              octoprint.plugin.RestartNeedingPlugin):

    def __init__(self): 
        self.hideTempTab = True
        self.hideControlTab = True
        self.hideGCodeTab = True
        self.helloCommand = "$$"
        self.statusCommand = "?"
        self.dwellCommand = "G4 P0.001"
        self.positionCommand = "?"
        self.suppressM114 = True
        self.suppressM400 = True
        self.suppressM105 = True
        self.suppressM115 = True
        self.suppressM110 = True
        self.disablePolling = True
        self.disableModelSizeDetection = True
        self.neverSendChecksum = True
        self.reOrderTabs = True
        self.reOrderSidebar = True
        self.disablePrinterSafety = True
        self.weakLaserValue = float(1)

        self.lastGCommand = ""

        self.overrideM8 = False
        self.overrideM9 = False
        self.m8Command = ""
        self.m9Command = ""

        self.grblMode = None
        self.grblState = None
        self.grblX = float(0)
        self.grblY = float(0)
        self.grblZ = float(0)
        self.grblA = float(0)
        self.grblB = float(0)
        self.offsets = []
        self.queue_Z = float(0)
        self.queue_X = float(0)
        self.queue_A = float(0)
        self.queue_B = float(0)
        self.grblActivePins = ""
        self.grblSpeed = float(0)
        self.grblPowerLevel = float(0)
        self.positioning = 0
        self.coolant = "M9"
        self.grblCoordinateSystem = "G54"
        self.babystep = 0
        self.match_cmd = re.compile(r"^(G[\d]+)\s?(G[\d]+)?\s?(G[\d]+)?.*")
        self.match_x = re.compile(r".*[Xx]\ *(-?[\d.]+).*")
        self.match_z = re.compile(r".*[Zz]\ *(-?[\d.]+).*")
        self.match_a = re.compile(r".*[Aa]\ *(-?[\d.]+).*")
        self.match_b = re.compile(r".*[Bb]\ *(-?[\d.]+).*")
        self.match_f = re.compile(r".*[Ff]\ *(-?[\d.]+).*")
        self.match_s = re.compile(r".*[Ss]\ *(-?[\d.]+).*")

        #default state will be to bypass RTCM
        self.RTCM = False
        #self.bypass_queuing = False
        self.do_bangle = False
        self.do_mod_a = False
        self.do_mod_z = False
        self.bangle = float(0)
        self.Afeed = False
        self.S_limit = False
        self.S_val = float(0)
        self.minFeed = float(0)
        self.DIAM = float(0)
        self.maxarc = float(0)
        self.arcadd = float(1)

        self.do_ovality = False
        self.template = False
        self.cut_depth = float(25)
        self.minZ = float(0)
        self.minZ_th = float(0.0)
        self.minZ_inc = float(0)
        self.track_plunge = False
        self.ignore_moda = False
        self.pauses_started = False
        self.queued_command = ""
        self.TERMINATE = False
        self.job_on_hold = False

        self.relative = False
        self.tooldistance = 135.0
        self.timeRef = 0
        
        self.grblErrors = {}
        self.grblAlarms = {}
        self.grblSettingsNames = {}
        self.grblSettings = {}
        self.grblSettingsText = ""

        self.ignoreErrors = False
        self.doSmoothie = False

        self.grblCmdQueue = []
        self.notifications = []

        self.grblVersion = "unknown"

        self.feedRate = float(0)
        self.plungeRate = float(0)
        self.powerRate = float(0)

        self.autoSleep = False
        self.autoSleepInterval = 20

        self.autoSleepTimer = time.time()

        self.autoCooldown = False
        self.autoCooldownFrequency = 60
        self.autoCooldownDuration = 15

        self.invertX = 1
        self.invertY = 1
        self.invertZ = 1

        self.connectionState = None
        self.pausedPower = 0
        self.pausedPositioning = 0

        self.trackedCmds = ["$CD", "$CONFIG/DUMP", "$$", "$+", "$S", "M115", "$SETTINGS/LIST", "$I", "$BUILD/INFO", "$G", "$GCODE/MODES"]
        self.lastRequest = []
        self.lastResponse = ""

        self.grblConfig = None

        self.fluidSettings = None
        self.fluidConfig = None
        self.fluidYaml = None

        self.noStatusRequests = False

        self.bgs_filters = [
            {"name": "Suppress status report requests", "regex": "^Send: \\?$"},
            {"name": "Suppress acknowledgement responses", "regex": "^Recv: ok$"},
            {"name": "Suppress status report responses", "regex": "^Recv: <.*[\\x2c|][WM]Pos:.+"},
            {"name": "Suppress blank responses", "regex": "^Recv: $"}
        ]

        self.octo_filters = [
            {
                "name": "Suppress temperature messages",
                "regex": r"(Send: (N\d+\s+)?M105)|(Recv:\s+(ok\s+([PBN]\d+\s+)*)?([BCLPR]|T\d*):-?\d+)",
            },
            {
                "name": "Suppress SD status messages",
                "regex": r"(Send: (N\d+\s+)?M27)|(Recv: SD printing byte)|(Recv: Not SD printing)",
            },
            {
                "name": "Suppress position messages",
                "regex": r"(Send:\s+(N\d+\s+)?M114)|(Recv:\s+(ok\s+)?X:[+-]?([0-9]*[.])?[0-9]+\s+Y:[+-]?([0-9]*[.])?[0-9]+\s+Z:[+-]?([0-9]*[.])?[0-9]+\s+E\d*:[+-]?([0-9]*[.])?[0-9]+).*",
            },
            {"name": "Suppress wait responses", "regex": "Recv: wait"},
            {
                "name": "Suppress processing responses",
                "regex": r"Recv: (echo:\s*)?busy:\s*processing",
            }
        ]

        self.bgsFilters = self.bgs_filters

        self.settingsVersion = 6
        self.wizardVersion = 15
        
        self.whenConnected = time.time()
        self.handshakeSent = False

        self.octoprintVersion = octoprint.server.VERSION
        self.a_profile = []

        # load up our item/value pairs for errors, warnings, and settings
        _bgs.load_grbl_descriptions(self)

    # #~~ SettingsPlugin mixin
    def get_settings_defaults(self):
        self._logger.debug("__init__: get_settings_defaults")

        return dict(
            hideTempTab = True,
            hideControlTab = True,
            hideGCodeTab = True,
            hello = "$$",
            statusCommand = "?",
            dwellCommand = "G4 P0.001",
            positionCommand = "?",
            suppressM114 = True,
            suppressM400 = True,
            suppressM105 = True,
            suppressM115 = True,
            suppressM110 = True,
            disablePolling = True,
            distance = float(1),
            control_distance = float(0),
            is_printing = False,
            is_operational = False,
            disableModelSizeDetection = True,
            neverSendChecksum = True,
            reOrderTabs = True,
            reOrderSidebar = True,
            disablePrinterSafety = True,
            grblSettingsText = None,
            grblSettingsBackup = "",
            weakLaserValue = float(1),
            overrideM8 = False,
            overrideM9 = False,
            m8Command = "",
            m9Command = "",
            ignoreErrors = False,
            doSmoothie = False,
            grblVersion = "unknown",
            laserMode = False,
            old_profile = "_default",
            useDevChannel = False,
            autoSleep = False,
            autoSleepInterval = 20,
            autoCooldown = False,
            autoCooldownFrequency = 60,
            autoCooldownDuration = 15,
            wizard_version = 1,
            invertX = False,
            invertY = False,
            invertZ = False,
            bgsFilters = self.bgs_filters,
            activeFilters = [],
            fluidYaml = None,
            fluidSettings = {},
            hasA = True,
            hasB = True,
            minZ_th = -1.0,
            track_plunge = False,
            
        )


    def on_after_startup(self):
        self._logger.debug("__init__: on_after_startup")
        self.datafolder = self.get_plugin_data_folder()

        # establish initial state for printer status
        self._settings.set_boolean(["is_printing"], self._printer.is_printing())
        self._settings.set_boolean(["is_operational"], self._printer.is_operational())

        # fix for V-Carve Grbl Toolpath referencing T1
        dest = self._settings.global_get_basefolder("printerProfiles") + os.path.sep + "_bgs.profile"

        if not os.path.exists(dest):
            src = os.path.dirname(os.path.realpath(__file__)) + os.path.sep + "static" + os.path.sep + "txt" + os.path.sep + "_bgs.profile"
            copyfile(src, dest)
            self._settings.set(["old_profile"], self._printer_profile_manager.get_current_or_default()["id"])
            self._printer_profile_manager.select("_bgs")
            self._printer_profile_manager.set_default("_bgs")
            self._logger.info("bgs printer profile created and selected")

        # let's only do stuff if our profile is selected
        if self._printer_profile_manager.get_current_or_default()["id"] != "_bgs":
            self._logger.info("bgs printer profile is not active")
            return

        # initialize all of our settings
        self.hideTempTab = self._settings.get_boolean(["hideTempTab"])
        self.hideControlTab = self._settings.get_boolean(["hideControlTab"])
        self.hideGCodeTab = self._settings.get_boolean(["hideGCodeTab"])

        self.helloCommand = self._settings.get(["hello"])
        self.statusCommand = self._settings.get(["statusCommand"])
        self.dwellCommand = self._settings.get(["dwellCommand"])
        self.positionCommand = self._settings.get(["positionCommand"])
        self.suppressM105 = self._settings.get_boolean(["suppressM105"])
        self.suppressM114 = self._settings.get_boolean(["suppressM114"])
        self.suppressM115 = self._settings.get_boolean(["suppressM115"])
        self.suppressM110 = self._settings.get_boolean(["suppressM110"])
        self.suppressM400 = self._settings.get_boolean(["suppressM400"])
        self.disablePolling = self._settings.get_boolean(["disablePolling"])

        self.disableModelSizeDetection = self._settings.get_boolean(["disableModelSizeDetection"])
        self.neverSendChecksum = self._settings.get_boolean(["neverSendChecksum"])

        self.reOrderTabs = self._settings.get_boolean(["reOrderTabs"])
        self.reOrderSidebar = self._settings.get_boolean(["reOrderSidebar"])

        self.overrideM8 = self._settings.get_boolean(["overrideM8"])
        self.overrideM9 = self._settings.get_boolean(["overrideM9"])
        self.m8Command = self._settings.get(["m8Command"])
        self.m9Command = self._settings.get(["m9Command"])

        self.ignoreErrors = self._settings.get(["ignoreErrors"])
        self.doSmoothie = self._settings.get(["doSmoothie"])

        self.weakLaserValue = float(self._settings.get(["weakLaserValue"]))

        self.grblSettingsText = self._settings.get(["grblSettingsText"])
        self.grblVersion = self._settings.get(["grblVersion"])

        self._settings.global_set_boolean(["feature", "modelSizeDetection"], not self.disableModelSizeDetection)
        self._settings.global_set_boolean(["feature", "sdSupport"], False)
        self._settings.global_set_boolean(["serial", "neverSendChecksum"], self.neverSendChecksum)

        self.autoSleep = self._settings.get_boolean(["autoSleep"])
        self.autoSleepInterval = round(float(self._settings.get(["autoSleepInterval"])))

        self.autoCooldown = self._settings.get_boolean(["autoCooldown"])
        self.autoCooldownFrequency = round(float(self._settings.get(["autoCooldownFrequency"])))
        self.autoCooldownDuration = round(float(self._settings.get(["autoCooldownDuration"])))

        self.invertX = -1 if self._settings.get_boolean(["invertX"]) else 1
        self.invertY = -1 if self._settings.get_boolean(["invertY"]) else 1
        self.invertZ = -1 if self._settings.get_boolean(["invertZ"]) else 1

        self._logger.debug("axis inversion X=[{}] Y=[{}] Z=[{}]".format(self.invertX, self.invertY, self.invertZ))

        fluidYaml = self._settings.get(["fluidYaml"])
        if not fluidYaml is None and len(fluidYaml) > 0:
            self.fluidYaml = yaml.safe_load(fluidYaml)

        self.fluidSettings = self._settings.get(["fluidSettings"])

        if self.neverSendChecksum:
            self._settings.global_set(["serial", "checksumRequiringCommands"], [])

        # initialize config.yaml disabled plugins list
        disabledPlugins = self._settings.global_get(["plugins", "_disabled"])
        if disabledPlugins == None:
            disabledPlugins = []

        # initialize config.yaml disabled tabs list
        disabledTabs = self._settings.global_get(["appearance", "components", "disabled", "tab"])
        if disabledTabs == None:
            disabledTabs = []

        # initialize config.yaml ordered tabs list
        orderedTabs = self._settings.global_get(["appearance", "components", "order", "tab"])
        if orderedTabs == None:
            orderedTabs = []

        # initialize config.yaml ordered sidebar list
        orderedSidebar = self._settings.global_get(["appearance", "components", "order", "sidebar"])
        if orderedSidebar == None:
            orderedSidebar = []

        # disable the printer safety check plugin
        if self.disablePrinterSafety:
            if "printer_safety_check" not in disabledPlugins:
                disabledPlugins.append("printer_safety_check")
        else:
            if "printer_safety_check" in disabledPlugins:
                disabledPlugins.remove("printer_safety_check")

        # disable the gcodeviewer plugin
        if self.hideGCodeTab:
            if "gcodeviewer" not in disabledPlugins:
                disabledPlugins.append("gcodeviewer")
            if "plugin_gcodeviewer" not in disabledTabs:
                disabledTabs.append("plugin_gcodeviewer")
        else:
            if "gcodeviewer" in disabledPlugins:
                disabledPlugins.remove("gcodeviewer")
            if "plugin_gcodeviewer" in disabledTabs:
                disabledTabs.remove("plugin_gcodeviewer")

        if self.hideTempTab:
            if "temperature" not in disabledTabs:
                disabledTabs.append("temperature")
        else:
            if "temperature" in disabledTabs:
                disabledTabs.remove("temperature")

        if self.hideControlTab:
            if "control" not in disabledTabs:
                disabledTabs.append("control")
        else:
            if "control" in disabledTabs:
                disabledTabs.remove("control")

        # ensure i am always the first tab
        if "plugin_latheengraversupport" in orderedTabs:
            orderedTabs.remove("plugin_latheengraver")
        if self.reOrderTabs:
            orderedTabs.insert(0, "plugin_latheengraver")

        # ensure i am at the top of the sidebar
        if "plugin_latheengraver" in orderedSidebar:
            orderedSidebar.remove("plugin_latheengraver")
        if self.reOrderSidebar:
            orderedSidebar.insert(0, "plugin_latheengraver")

        self._settings.global_set(["plugins", "_disabled"], disabledPlugins)
        self._settings.global_set(["appearance", "components", "disabled", "tab"], disabledTabs)
        self._settings.global_set(["appearance", "components", "order", "tab"], orderedTabs)
        self._settings.global_set(["appearance", "components", "order", "sidebar"], orderedTabs)

        # add pretty much all of grbl to long running commands list
        longCmds = self._settings.global_get(["serial", "longRunningCommands"])
        if longCmds == None:
            longCmds = []

        if not "$H" in longCmds: longCmds.append("$H")
        if not "G92" in longCmds: longCmds.append("G92")
        if not "G30" in longCmds: longCmds.append("G30")
        if not "G53" in longCmds: longCmds.append("G53")
        if not "G54" in longCmds: longCmds.append("G54")

        if not "G20" in longCmds: longCmds.append("G20")
        if not "G21" in longCmds: longCmds.append("G21")

        if not "G90" in longCmds: longCmds.append("G90")
        if not "G91" in longCmds: longCmds.append("G91")
        if not "G93" in longCmds: longCmds.append("G93")

        if not "G38.1" in longCmds: longCmds.append("G38.1")
        if not "G38.2" in longCmds: longCmds.append("G38.2")
        if not "G38.3" in longCmds: longCmds.append("G38.3")
        if not "G38.4" in longCmds: longCmds.append("G38.4")
        if not "G38.5" in longCmds: longCmds.append("G38.5")

        if not "G0" in longCmds: longCmds.append("G0")
        if not "G1" in longCmds: longCmds.append("G1")
        if not "G2" in longCmds: longCmds.append("G2")
        if not "G3" in longCmds: longCmds.append("G3")
        if not "G4" in longCmds: longCmds.append("G4")

        if not "M3" in longCmds: longCmds.append("M3")
        if not "M4" in longCmds: longCmds.append("M4")
        if not "M5" in longCmds: longCmds.append("M5")
        if not "M7" in longCmds: longCmds.append("M7")
        if not "M8" in longCmds: longCmds.append("M8")
        if not "M9" in longCmds: longCmds.append("M9")
        if not "M30" in longCmds: longCmds.append("M30")

        self._settings.global_set(["serial", "longRunningCommands"], longCmds)
        self._settings.global_set(["serial", "maxCommunicationTimeouts", "long"], 0)
        self._settings.global_set(["serial", "encoding"], "latin_1")
        self._settings.global_set_boolean(["serial", "sanityCheckTools"], False)

        self._settings.global_set(["terminalFilters"], self.bgsFilters)

        self._settings.save()

        # remove scripts/gcode/afterPrintCancelled because it does stupid stuff with tools
        oldCancelScript = os.path.realpath(os.path.join(self._settings.global_get_basefolder("scripts"), "gcode", "oldAfterPrintCancelled"))
        currentCancelScript = os.path.realpath(os.path.join(self._settings.global_get_basefolder("scripts"), "gcode", "afterPrintCancelled"))

        if not os.path.exists(oldCancelScript) and os.path.exists(currentCancelScript):
            os.rename(currentCancelScript, oldCancelScript)

        _bgs.load_grbl_settings(self)


    def get_settings_version(self):
        self._logger.debug("__init__: get_settings_version")
        return self.settingsVersion


    def on_settings_migrate(self, target, current):
        self._logger.debug("__init__: on_settings_migrate target=[{}] current=[{}]".format(target, current))

        if current == None or current != target:
            orderedTabs = self._settings.global_get(["appearance", "components", "order", "tab"])
            if "gcodeviewer" in orderedTabs:
                orderedTabs.remove("gcodeviewer")
                self._settings.global_set(["appearance", "components", "order", "tab"], orderedTabs)

            disabledTabs = self._settings.global_get(["appearance", "components", "disabled", "tab"])
            if "gcodeviewer" in disabledTabs:
                disabledTabs.remove("gcodeviewer")
                self._settings.global_set(["appearance", "components", "disabled", "tab"], disabledTabs)

            if self._settings.get(["statusCommand"]) == "?$G":
                self._settings.set(["statusCommand"], "?")
                self.statusCommand = "?"

            self._settings.set(["dwellCommand"], "G4 P0.001")
            self.dwellCommand = "G4 P0.001"

            self._settings.remove(["showZ"])
            self._settings.remove(["distance"])
            self._settings.remove(["customControls"])

            self._settings.save()
            self._logger.info("Migrated to settings v%d from v%d", target, 1 if current == None else current)


    def on_settings_save(self, data):
        self._logger.debug("__init__: on_settings_save data=[{}]".format(data))
        # let's only do stuff if our profile is selected
        if self._printer_profile_manager.get_current_or_default()["id"] != "_bgs":
            return

        self._logger.debug("saving settings")
        octoprint.plugin.SettingsPlugin.on_settings_save(self, data)

        # pause status requests
        self.noStatusRequests = True

        # reload our config
        self.on_after_startup()

        if not self._printer.is_printing(): 
            if "fluidYaml" in data or "fluidSettings" in data:
                # save our fluid config
                if "fluidYaml" in data:
                    self.fluidConfig = data.get("fluidYaml")
                    self.fluidYaml = yaml.safe_load(data.get("fluidYaml"))

                    if self.fluidSettings.get("HTTP/Enable").upper() == "ON":
                        try:
                            url = "http://{}:{}/files".format(self.fluidSettings.get("Hostname"), self.fluidSettings.get("HTTP/Port"))
                            params = {'action': 'delete', 'filename': self.fluidSettings.get("Config/Filename")}
                            r = requests.get(url, params)
                            r.close()

                            # lets wait a second for fluid to settle down
                            time.sleep(1)

                            files = {'file': (self.fluidSettings.get("Config/Filename"), self.fluidConfig)}
                            r = requests.post(url, files=files)
                            r.close()

                            if not "fluidSettings" in data:
                                _bgs.queue_cmds_and_send(self, ["$Bye"])
                        except Exception as e:
                            self._logger.warn("__init__: on_settings_save unable to save fluid config: {}".format(e))
                            _bgs.update_fluid_config(self)
                    else: 
                        _bgs.update_fluid_config(self)

                # save our fluid settings
                if "fluidSettings" in data:
                    for key, value in data.get("fluidSettings", {}).items():
                        self._printer.commands("${}={}".format(key, value))

                    if "fluidYaml" in data:
                        _bgs.queue_cmds_and_send(self, ["$Bye"])
                    else:
                        _bgs.queue_cmds_and_send(self, ["$Bye", "$CD"])
    
                # refresh our grbl settings
                if not _bgs.is_grbl_fluidnc(self):
                    if self.doSmoothie:
                        self._printer.commands("Cat /sd/config")
                    else:
                        self._printer.commands("$+" if _bgs.is_grbl_esp32(self) else "$$")

        # resume status requests (after 10 seconds)
        threading.Thread(target=_bgs.defer_resuming_status_reports, args=(self, 10, "fluidYaml" in data or "fluidSettings" in data)).start()


    # #~~ AssetPlugin mixin
    def get_assets(self):
        self._logger.debug("__init__: get_assets")

        # Define your plugin's asset files to automatically include in the
        # core UI here.
        return dict(js=['js/latheengraver.js', 'js/latheengraver_settings.js', 
                        'js/latheengraver_wizard.js', 'js/bgs_terminal.js'],
                    css=['css/latheengraver.css', 'css/latheengraver_settings.css'],
                    less=['less/latheengraver.less', "less/latheengraver.less"])


    # #~~ TemplatePlugin mixin
    def get_template_configs(self):
        self._logger.debug("__init__: get_template_configs")

        return [
            {
                    "type": "settings",
                    "template": "latheengraver_settings.jinja2",
                    "custom_bindings": True
            },
            {
                    "type": "wizard",
                    "name": "Better Grbl Support",
                    "template": "latheengraver_wizard.jinja2",
                    "custom_bindings": True
            }
        ]


    # #-- EventHandlerPlugin mix-in
    def on_event(self, event, payload):
        _bgs.on_event(self, event, payload)


    def on_plugin_pending_uninstall(self):  # this will work in some next release of octoprint
        self._logger.debug("__init__: on_plugin_pending_uninstall")

        self._logger.debug('we are being uninstalled via on_plugin_pending_uninstall :(')
        _bgs.cleanup_due_to_uninstall(self)
        self._logger.debug('uninstall cleanup completed (this house is clean)')


    def get_extension_tree(self, *args, **kwargs):
        return dict(
                model=dict(
        		grbl_gcode=["gc", "nc"]
                )
        )

    def hook_script_onresume(self, comm, script_type, script_name, *args, **kwargs):
        self._logger.info(script_type, script_name)
        if not script_type == "gcode" or not script_name == "beforePrintResumed":
            return None
        positioning = "G91" if self.pausedPositioning == 1 else "G90"
        prefix = ["~","M3","G4 P5",positioning]
        if self.queued_command:
            postfix=self.queued_command
            self.queued_command = ""
        else:
            postfix = None
        return prefix, postfix
    
    # #-- gcode queuing hook
    #these need to be in queuing to extend
    def hook_gcode_queuing(self, comm_instance, phase, cmd, cmd_type, gcode, tags, *args, **kwargs):
        
        #only alter commands if we are running a job
        if not self._printer.is_printing():
             return cmd
         
        if cmd.upper() == "RTCM":
            self.RTCM = True
            self._logger.info("Real-time coordinate modification activated")
            return cmd
        
        #if terminate has started, we aren't going to queue or send any more gcode, all commands are skipped
        if self.TERMINATE and cmd.upper() != "M30":
            cmd = None, 
            return cmd
        
        if not self.RTCM:
            return cmd
        
        assembly = {"X": None, "Z": None, "A": None, "B": None, "F": None, "S": None}
        track_plunge = False
        orig_cmd = cmd
        #this is needed because B axis moves may not be emitted.
        self.queue_B = self.grblB
        newcmd = ''
        match_cmd = self.match_cmd.match(cmd)
        gcommands = []
        moves = ["G1", "G01", "G0", "G00"]
         
        match_x = self.match_x.match(cmd)
        match_z = self.match_z.match(cmd)
        match_a = self.match_a.match(cmd)
        match_b = self.match_b.match(cmd)
        match_f = self.match_f.match(cmd)
        match_s = self.match_s.match(cmd)
        #Have to track position resets...hmmm
        #this is hacky. why does it put a 1 into the list if not present?
        if not match_cmd:
            return cmd
        if match_cmd.groups(1)[0] != 1: gcommands.append(match_cmd.groups(1)[0])
        if match_cmd.groups(1)[1] != 1: gcommands.append(match_cmd.groups(1)[1])
        if match_cmd.groups(1)[2] != 1: gcommands.append(match_cmd.groups(1)[2])
        if not any(c in gcommands for c in moves):
            return cmd
        for c in gcommands:
            newcmd = newcmd + "{0}".format(c)
            #assembly["COMM"] = "{0} ".format(c)
        self._logger.debug("new command is: {}".format(newcmd))
        self._logger.debug(f"Template: {self.template}, Depth: {self.cut_depth}, queue_z: {self.queue_Z}")
        #single axis match things first
        if match_z:
            self.queue_Z = float(match_z.groups(1)[0])
            
            #template must be checked, cut_depth must be non-zero and the value must be less than cut_depth to start termination
            if self.template and (self.cut_depth < 0) and (self.queue_Z < self.cut_depth):
                self.start_termination()
                cmd = (None, )
                return cmd
            
            if self.track_plunge:
                if self.pauses_started and self.minZ_inc:
                    if (self.queue_Z <= self.minZ-self.minZ_inc):
                        self.minZ = self.queue_Z
                        track_plunge = True
                if self.pauses_started and not self.minZ_inc:
                    if (self.queue_Z < self.minZ):
                        self.minZ = self.queue_Z
                        track_plunge = True
                if not self.pauses_started and (self.queue_Z < self.minZ_th) and (self.queue_Z < self.minZ):
                    self.minZ = self.queue_Z
                    self.pauses_started = True
                    self._logger.info("Zmin now {0}".format(self.minZ))
                    track_plunge = True
        
        if track_plunge:
            self.queued_command = orig_cmd
            #self._logger.info(self.queued_command)
            if self._printer.set_job_on_hold(True):
                self._printer.pause_print()
                cmd="M5"
                self._printer.set_job_on_hold(False)
                return cmd
              
        if match_x:
            self.queue_X = float(match_x.groups(1)[0])
        if match_a:
            self.queue_A = float(match_a.groups(1)[0])
        if match_b:
            self.queue_B = float(match_b.groups(1)[0])
            assembly["B"] = self.queue_B
        if match_f:
            self.queue_F = float(match_f.groups(1)[0])
            if self.Afeed:
                if self.queue_F < self.minFeed:
                    self.queue_F = self.minFeed
            if self.feedRate != 0:
                self.queue_F = self.queue_F * self.feedRate
            assembly["F"] = self.queue_F
        if match_s:
            self.queue_S = float(match_s.groups(1)[0])
            if self.S_limit:
                if self.queue_S > self.S_val:
                    self.queue_S = self.S_val
            assembly["S"] = self.queue_S

        #begin multi-axis conditional things with modified coordinates
        #these will hold the modifiers for any coordinate values
        mod_x = 0
        mod_z = 0.0
        trans_x = self.queue_X
        trans_z = self.queue_Z
        trans_a = self.queue_A
        zmod = 0.0
        if match_x or match_z or match_a or match_b:

            if self.do_mod_z:
                zmod = self.adjust_Z(self.queue_A, self.queue_Z)
                #zmod is some difference that gets subtracted from Z based on A angle
                #self._logger.info("Z modified by {0}".format(zmod)

            if self.do_ovality:
                #mod_z is some difference
                mod_z = self.get_depth_mod(self.queue_A)
                if not self.do_bangle:
                    bangle = math.radians(self.queue_B)*-1
                    #get the relative change in x and z based on change in z and the b angle
                    trans_x = self.queue_X - mod_z*math.sin(bangle)
                    trans_z = self.queue_Z - mod_z*math.cos(bangle)
                self._logger.debug("ovality mod_z is: {}".format(mod_z))

            if self.do_bangle: 
                bangle = math.radians(self.queue_B)*-1
                #this could use some cleanup
                delta_x = mod_z*math.sin(bangle)
                delta_z = mod_z*math.cos(bangle)
                trans_x = self.queue_X*math.cos(bangle) + (self.queue_Z - zmod)*math.sin(bangle) - delta_x
                trans_z = -self.queue_X*math.sin(bangle) + (self.queue_Z - zmod)*math.cos(bangle) - delta_z
                trans_z_init = -self.queue_X*math.sin(bangle) + (0 - zmod)*math.cos(bangle) - delta_z

                if self.do_mod_a:
                    trans_a, deltaZ = self.get_new_A(trans_z_init, self.queue_A)
                    trans_z = trans_z+deltaZ
            
        assembly["X"] = trans_x
        assembly["Z"] = trans_z
        assembly["A"] = trans_a
        assembly["B"] = self.queue_B
        self._logger.debug("assembly is: {}".format(assembly))
        self._logger.debug("original values: X{0} Z{1}".format(self.queue_X, self.queue_Z))
        cmd = self.assemble_command(newcmd, assembly)
        return cmd

    def assemble_command(self, newcmd, assembly):
        cmd = newcmd
        for key, value in assembly.items():
            if value is not None:
                cmd = cmd+" {0}{1:.4f}".format(str(key), value)
        return cmd
    
    def get_new_A(self, zval, aval):
        radius = self.DIAM/2
        calc_Arad = math.radians(float(aval))
        calc_Y = calc_Arad*(radius)
        distance = math.sqrt(calc_Y**2 + (radius + zval)**2)
        to_origin = math.sqrt(calc_Y**2 + zval**2)
        cos_angle = (radius**2 + distance**2 - to_origin**2) / (2 * radius * distance)
        cos_angle = sorted([-1, cos_angle, 1])[1]
        new_A = math.acos(cos_angle)
       
        if calc_Y < 0:
            new_A = new_A*-1
        local_distance = distance - radius - zval
        self._logger.debug("Calc. Y: {0:.2f}, Distance: {1:.2f}, To Origin: {2:.2f}, Degrees: {3:.2f}, Zval: {4:.2f}".format(calc_Y, distance, to_origin, math.degrees(new_A), zval))
        return math.degrees(new_A), local_distance

    def get_a_profile(self, profile):
        self.a_profile = []
        try: 
            with open(profile, 'r') as file:
                lines = file.readlines()
                first_z, first_a = None, None
                for line in lines:
                    line = line.strip()
                    # Skip lines that begin with a semicolon
                    if line.startswith(';'):
                        continue
                    # Split the line into x and y components
                    z_str, a_str = line.split(',')
                    z, a = float(z_str), float(a_str)
            
                    if first_z is None and first_a is None:
                        # This is the first data point, set as reference
                        first_z, first_a = z, a
            
                    # Make the data points relative to the first data point
                    relative_z = first_z - z #flipped
                    relative_a = a - first_a
            
                    # Add the relative coordinates as a tuple to the list
                    self.a_profile.append((float(format(relative_z, '.3f')), int(relative_a)))
                #add first entry back as 360 degrees
                self.a_profile.append((0.0,360))
        except:
            self._logger.info("Could not load profile. Ovality correction not active")
            self.do_ovality = False

        self._logger.debug("Profile loaded with {0} points".format(len(self.a_profile)))
        self._logger.debug(self.a_profile)

    def get_depth_mod(self, aval):
        """
        returns the Z value depth difference based on a scan around the a-axis (a_profile)
        """
        normal_aval = aval % 360
        if normal_aval < 0:
            normal_aval += 360
        #linearly interpolate and return the depth (Z) difference
        for i in range(len(self.a_profile) - 1):
            z1, a1 = self.a_profile[i]
            z2, a2 = self.a_profile[i + 1]
            if a1 <= normal_aval <= a2:
                # Perform linear interpolation
                depth_value = z1 + (z2 - z1) * (normal_aval - a1) / (a2 - a1)
                return depth_value

    def adjust_Z(self, aval, zval):
        modDiam = (self.DIAM/2) + zval
        aval = math.radians(aval)
        #in case weird things happen
        if aval > self.maxarc/2:
            return 0.0
        diff = math.sqrt(((self.maxarc/2)**2) - (aval**2))
        zmod = modDiam - (modDiam*math.cos(diff))
        return zmod*self.arcadd
    
    #Not currently used, might want to revisit later
    def rot_trans_adjust(self, bvalues):
        #get absolute positions first
        bangle = self.grblB + bvalues
        currentx = self.grblX
        currentz = self.grblZ

        bangle = math.radians(bangle)*-1
        #mod_x = currentx*math.cos(bangle) + (currentz + self.tooldistance)*math.sin(bangle)
        mod_x = self.tooldistance*math.sin(math.radians(bvalues))
        mod_z = self.tooldistance*math.cos(bangle) - self.tooldistance
        #mod_z = self.tooldistance*math.cos(bangle) - self.tooldistance

        return mod_x, mod_z
    
    def start_termination(self):
        #need these commands to be queued, so don't use Force
        self._printer.commands(["G0 Z5", "M5", "M30", "TERMINATE"], force=True)
    
    # #-- gcode sending hook
    def hook_gcode_sending(self, comm_instance, phase, cmd, cmd_type, gcode, *args, **kwargs):
        self._logger.debug("__init__: hook_gcode_sending phase=[{}] cmd=[{}] cmd_type=[{}] gcode=[{}]".format(phase, cmd, cmd_type, gcode))
        # let's only do stuff if our profile is selected
        if self._printer_profile_manager.get_current_or_default()["id"] != "_bgs":
            return None

        cmd = cmd.lstrip("\r").lstrip("\n").rstrip("\r").rstrip("\n")

        # suppress temperature if machine is printing
        if "M105" in cmd.upper() or cmd.startswith(self.statusCommand):
            if (self.disablePolling and self._printer.is_printing()) or len(self.lastRequest) > 0 or self.noStatusRequests:
                self._logger.debug('Ignoring %s', cmd)
                return (None, )
            else:
                if self.suppressM105:
                    # go to sleep if autosleep and now - last > interval
                    # self._logger.debug("autosleep enabled={} interval={} timer={} time={} diff={}".format(self.autoSleep, self.autoSleepInterval, self.autoSleepTimer, time.time(), time.time() - self.autoSleepTimer))
                    if self.autoSleep and time.time() - self.autoSleepTimer > self.autoSleepInterval * 60:
                        if self.grblState.upper() != "SLEEP" and self._printer.is_operational() and not self._printer.is_printing():
                            _bgs.queue_cmds_and_send(self, ["$SLP"])
                        else:
                            self._logger.debug("resetting autosleep timer")
                            self.autoSleepTimer = time.time()

                    self._logger.debug('Rewriting M105 as %s' % self.statusCommand)
                    return (self.statusCommand, )

        self.autoSleepTimer = time.time()

        # hack for unacknowledged grbl commmands
        if "$H" in cmd.upper() or "G38.2" in cmd.upper():
            # threading.Thread(target=_bgs.do_fake_ack, args=(self._printer, self._logger)).start()
            # self._logger.debug("fake_ack submitted")
            self.grblState = "Home" if "$H" in cmd.upper() else "Run"
            self._plugin_manager.send_plugin_message(self._identifier, dict(type="grbl_state", state="Run"))

        # suppress comments and extraneous commands that may cause wayward
        # grbl instances to error out
        if cmd.upper().startswith((";", "(", "%")):
            self._logger.debug('Ignoring extraneous [%s]', cmd)
            return (None, )

        # suppress reset line #s
        if self.suppressM110 and cmd.upper().startswith('M110'):
            self._logger.debug('Ignoring %s', cmd)

            if self.connectionState == Events.CONNECTING and not self.handshakeSent:
                self._logger.debug("sending initial handshake")
                self.handshakeSent = True
                cmd = "\n\n\x18"
            else:
                return (None, )

        # suppress initialize SD - M21
        if cmd.upper().startswith('M21'):
            self._logger.debug('Ignoring %s', cmd)
            return (None,)

        # ignore all of these -- they do not apply to GRBL
        # M108 (heater off)
        # M84 (disable motors)
        # M104 (set extruder temperature)
        # M140 (set bed temperature)
        # M106 (fan on/off)
        # N -- suggests a line number and we don't roll like that
        if cmd.upper().startswith(("M108", "M84", "M104", "M140", "M106", "N")):
            self._logger.debug("ignoring [%s]", cmd)
            return (None, )

        # forward on coordinate system change
        if cmd.upper() in ("G54", "G55", "G56", "G57", "G58", "G59"):
            self.grblCoordinateSystem = cmd.upper()
            self._plugin_manager.send_plugin_message(self._identifier, dict(type="grbl_state", coord=self.grblCoordinateSystem))

        # M8 (air assist on) processing - work in progress
        if cmd.upper() in ("M7", "M8"):
            self.coolant = cmd.upper()
            self._plugin_manager.send_plugin_message(self._identifier, dict(type="grbl_state", colant=self.coolant))

            if self.overrideM8 and cmd.upper() == "M8":
                self._logger.debug('Turning ON Air Assist')
                subprocess.call(self.m8Command, shell=True)

                return (None,)

        # M9 (air assist off) processing - work in progress
        if cmd.upper() == "M9":
            self.coolant = cmd.upper()
            self._plugin_manager.send_plugin_message(self._identifier, dict(type="grbl_state", colant=self.coolant))

            if self.overrideM9:
                self._logger.debug('Turning OFF Air Assist')
                subprocess.call(self.m9Command, shell=True)

                return (None,)
        if cmd.upper() == "G91":
            self.relative = True
            self._logger.info("Relative mode")
            return (cmd, )
        if cmd.upper() == "G90":
            self._logger.info("Absolute mode")
            self.relative = False
            return (cmd, )
        if cmd.upper() == "DOBANGLE":
            self.do_bangle = True
            #turn on RTCM as well
            self.RTCM = True
            self.bangle = self.grblB
            self._logger.info('do_bangle is: {0} and bangle is: {1}'.format(self.do_bangle, self.bangle))
            #set B to current position to make sure motor is engaged
            newcmd = "G90 G1 B{0} F200".format(self.grblB)
            return (newcmd, )
        
        if cmd.upper() == "STOPBANGLE":
            self.do_bangle = False
            self._logger.info('B angle matrix transformation off')
            return (None, )
        
        if cmd.upper() == "TERMINATE":
            self.TERMINATE = True
            self._logger.info("Termination initiated")
            return (None, )
        
        if cmd.upper() == "DOMODA":
            self._logger.info(f'DOMODA hit, ignore_moda is {self.ignore_moda}')
            if self.ignore_moda:
                self.do_mod_a = False
                self._logger.info('Depth modification disabled in run setup')
                return (None, )
            else:
                self.do_mod_a = True
                self.RTCM = True
                self._logger.info('Depth modification enabled')
                return (None, )
        
        if cmd.upper() == "STOPMODA":
            self.do_mod_a = False
            self._logger.info('Depth modification inactive')
            return (None, )
        if cmd.upper() == "DOARCMOD":
            self.do_mod_z = True
            self.RTCM = True
            return (None, )
        if cmd.upper() == "STOPARCMOD":
            self.do_mod_z = False
            return (None, )
        if cmd.upper().startswith("MAXARC"):
            minmax_match = re.search(r"MAXARC ([\d.]+)", cmd)
            if minmax_match:
                self.maxarc = math.radians(float(minmax_match.groups(1)[0]))
                #self.do_mod_z = True
                self._logger.info("MAXARC set to {0}".format(self.maxarc))
                if self.maxarc == 0.0:
                    self.do_mod_z = False 
                    self._logger.info("MAXARC inactive")
                
            return (None, )
        
        if cmd.upper().startswith("ARCADD"):
            arcadd_match = re.search(r"ARCADD ([\d.]+)", cmd)
            if arcadd_match:
                self._logger.info("ARCADD set to {0}".format(self.maxarc))
                self.arcadd = float(arcadd_match.groups(1)[0])
            return (None, )

        if cmd.upper().startswith("AFEED"):
            diam_match = re.search(r"AFEED ([\d.]+)", cmd)
            if diam_match:
                self.Afeed = True
                self.minFeed = float(diam_match.groups(1)[0])
            if self.minFeed < 1.0:
                self.Afeed = False
            self._logger.info('Afeed is: {0} and diameter is: {1}'.format(self.Afeed, self.minFeed))
            return (None, )
        
        if cmd.upper().startswith("SLIMIT"):
            s_match = re.search(r"SLIMIT ([\d.]+)", cmd)
            if s_match:
                self.S_limit = True
                self.S_val = float(s_match.groups(1)[0])
            if self.S_val < 1.0:
                self.S_limit = False
            self._logger.info('Power limit is: {0}'.format(self.S_val))
            return (None, )
        
        if cmd.upper().startswith("DIAM"):
            diam_match = re.search(r"DIAM ([\d.]+)", cmd)
            if diam_match:
                self.DIAM = float(diam_match.groups(1)[0])
                self._logger.info('Diameter set: {0}'.format(self.DIAM))
            return (None, )
        
        if cmd.upper() == "RTCM":
            self.RTCM = True
            self._logger.info("Real-time coordinate modification activated")
            return (None, )
        
        if cmd.upper() == "STOPRTCM":
            self.RTCM = False
            self._logger.info("Real-time coordinate modification not activated")
            return (None, )

        # Grbl 1.1 Realtime Commands (requires Octoprint 1.8.0+)
        # see https://github.com/OctoPrint/OctoPrint/pull/4390

        # safety door
        if cmd.upper() == "SAFETYDOOR":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Triggering safety door ")
                cmd = "? {} ?".format("\x84")
            else:
                return (None, )

        # cancel jog
        if cmd.upper() == "CANCELJOG":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Cancelling jog")
                cmd = "? {} ?".format("\x85")
            else:
                return (None, )

        # normal feed
        if cmd.upper() == "FEEDNORMAL":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Setting normal feed rate")
                cmd = "? {} ?".format("\x90")
            else:
                return (None, )

        # feed +10%
        if cmd.upper() == "FEEDPLUS10":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Setting feed rate +10%")
                cmd = "? {} ?".format("\x91")
            else:
                return (None, )

        # feed -10%
        if cmd.upper() == "FEEDMINUS10":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Setting feed rate -10%")
                cmd = "? {} ?".format("\x92")
            else:
                return (None, )

        # feed +1%
        if cmd.upper() == "FEEDPLUS1":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Setting feed rate +1%")
                cmd = "? {} ?".format("\x93")
            else:
                return (None, )

        # feed -1%
        if cmd.upper() == "FEEDMINUS1":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Setting feed rate -1%")
                cmd = "? {} ?".format("\x94")
            else:
                return (None, )

        # normal spindle
        if cmd.upper() == "SPINDLENORMAL":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Setting normal spindle speed")
                cmd = "? {} ?".format("\x99")
            else:
                return (None, )

        # spindle +10%
        if cmd.upper() == "SPINDLEPLUS10":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Setting spindle speed +10%")
                cmd = "? {} ?".format("\x9a") 
            else:
                return (None, )

        # spindle -10%
        if cmd.upper() == "SPINDLEMINUS10":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Setting spindle speed -10%")
                cmd = "? {} ?".format("\x9B")
            else:
                return (None, )

        # spindle +1%
        if cmd.upper() == "SPINDLEPLUS1":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Setting spindle speed +1%")
                cmd = "? {} ?".format("\x9C")
            else:
                return (None, )

        # spindle -1%
        if cmd.upper() == "SPINDLEMINUS1":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Setting spindle speed -1%")
                cmd = "? {} ?".format("\x9D")
            else:
                return (None, )

        # toggle spindle
        if cmd.upper() == "TOGGLESPINDLE":
            if _bgs.is_grbl_one_dot_one(self) and _bgs.is_latin_encoding_available(self):
                self._logger.debug("Toggling spindle stop")
                cmd = "? {} ?".format("\x9E")
            else:
                return (None, )

        # rewrite M115 firmware as $$ (hello)
        if self.suppressM115 and cmd.upper().startswith('M115'):
            self._logger.debug('Rewriting M115 as %s' % self.helloCommand)

            # let's not be in too big of a rush
            time.sleep(.5)

            if self.doSmoothie:
                self.lastRequest.append("$$")
                return "Cat /sd/config"

            cmd = "$+" if _bgs.is_grbl_esp32(self) else self.helloCommand

            # in the unlikely event our hello command has been remapped
            if not cmd.upper() in self.trackedCmds:
                self.trackedCmds.append(cmd.upper())
        
        # Wait for moves to finish before turning off the spindle
        if self.suppressM400 and cmd.upper().startswith('M400'):
            self._logger.debug('Rewriting M400 as %s' % self.dwellCommand)
            cmd = self.dwellCommand

        # rewrite M114 current position as ? (typically)
        if self.suppressM114 and cmd.upper().startswith('M114'):
            self._logger.debug('Rewriting M114 as %s' % self.positionCommand)
            cmd = self.positionCommand

        # soft reset / resume (stolen from Marlin)
        if cmd.upper().startswith('M999') and not self.doSmoothie:
            self._logger.debug('Sending Soft Reset')
            _bgs.add_notifications(self, ["Machine has been reset"])

            self.grblState = "Reset"
            self._plugin_manager.send_plugin_message(self._identifier, dict(type="grbl_state", state="Reset"))
            _bgs.queue_cmds_and_send(self, ["$G"])

            # sanity check on reset
            self.lastRequest = []
            self.lastResponse = ""

            cmd = "\x18"

        # grbl version info
        if cmd.upper().startswith("$I"):
            self.grblVersion = ""
            self.fluidYaml = ""
            self._settings.set(["grblVersion"], self.grblVersion)
            self._settings.set(["fluidYaml"], self.fluidYaml)
            self._settings.save(trigger_event=True)

        # we need to track absolute position mode for "RUN" position updates
        if "G90" in cmd.upper():
            # absolute positioning
            self.positioning = 0
            self._plugin_manager.send_plugin_message(self._identifier, dict(type="grbl_state", positioning=self.positioning))

        # we need to track relative position mode for "RUN" position updates
        if "G91" in cmd.upper():
            # relative positioning
            self.positioning = 1
            self._plugin_manager.send_plugin_message(self._identifier, dict(type="grbl_state", positioning=self.positioning))

        # save our G command for shorthand post processors
        if cmd.upper().startswith("G"):
            self.lastGCommand = cmd[:3] if cmd[2:3].isnumeric() else cmd[:2]

        # use our saved G command if our line starts with a coordinate
        if cmd.upper().startswith(("X", "Y", "Z")):
            cmd = self.lastGCommand + " " + cmd

        # keep track of distance traveled
        found = False
        foundZ = False

        # match = re.search(r"^G([0][0123]|[0123])(\D.*[Xx]|[Xx])\ *(-?[\d.]+).*", command)
        match = re.search(r".*[Xx]\ *(-?[\d.]+).*", cmd)
        if not match is None:
            self.grblX = float(match.groups(1)[0]) if self.positioning == 0 else self.grblX + float(match.groups(1)[0])
            found = True

        # match = re.search(r"^G([0][0123]|[0123])(\D.*[Yy]|[Yy])\ *(-?[\d.]+).*", command)
        match = re.search(r".*[Yy]\ *(-?[\d.]+).*", cmd)
        if not match is None:
            self.grblY = float(match.groups(1)[0]) if self.positioning == 0 else self.grblY + float(match.groups(1)[0])
            found = True

        # match = re.search(r"^G([0][0123]|[0123])(\D.*[Zz]|[Zz])\ *(-?[\d.]+).*", command)
        match = re.search(r".*[Zz]\ *(-?[\d.]+).*", cmd)
        if not match is None:
            self.grblZ = float(match.groups(1)[0]) if self.positioning == 0 else self.grblZ + float(match.groups(1)[0])
            found = True
            foundZ = True
            #Don't let deep cuts get through
            if self.template and self.cut_depth and self.queue_Z < self.cut_depth:
                return (None, )

        #ADD A and B here
        match = re.search(r".*[Aa]\ *(-?[\d.]+).*", cmd)
        if not match is None:
            self.grblA = float(match.groups(1)[0]) if self.positioning == 0 else self.grblA + float(match.groups(1)[0])
            found = True

        match = re.search(r".*[Bb]\ *(-?[\d.]+).*", cmd)
        if not match is None:
            self.grblB = float(match.groups(1)[0]) if self.positioning == 0 else self.grblB + float(match.groups(1)[0])
            found = True
        
        # match = re.search(r"^[GM]([0][01234]|[01234])(\D.*[Ff]|[Ff])\ *(-?[\d.]+).*", command)
        match = re.search(r".*[Ff]\ *(-?[\d.]+).*", cmd)
        if not match is None:
            grblSpeed = float(match.groups(1)[0])
            # make sure we post all speed on / off events
            if (grblSpeed == 0 and self.grblSpeed != 0) or (self.grblSpeed == 0 and grblSpeed != 0):
                self.timeRef = 0

            self.grblSpeed = grblSpeed
            found = True
        
        # match = re.search(r"^[GM]([0][01234]|[01234])(\D.*[Ss]|[Ss])\ *(-?[\d.]+).*", command)
        match = re.search(r".*[Ss]\ *(-?[\d.]+).*", cmd)
        if not match is None:
            grblPowerLevel = float(match.groups(1)[0])

            # check if power rate is overridden
            if self.powerRate != 0 and grblPowerLevel != 0:
                grblPowerLevel = grblPowerLevel * self.powerRate
                cmd = cmd.upper().replace("S" + match.groups(1)[0], "S{:.3f}".format(grblPowerLevel))
                cmd = cmd.upper().replace("S " + match.groups(1)[0], "S {:.3f}".format(grblPowerLevel))
                # self._logger.debug("power rate modified from [{}] to [{}]".format(match.groups(1)[0], grblPowerLevel))

            # make sure we post all power on / off events
            self.grblPowerLevel = grblPowerLevel
            found = True

        if found:
            currentTime = int(round(time.time() * 1000))
            if currentTime > self.timeRef + 250:
                # self._logger.info("x=[{}] y=[{}] z=[{}] f=[{}] s=[{}]".format(self.grblX, self.grblY, self.grblZ, self.grblSpeed, self.grblPowerLevel))
                self._plugin_manager.send_plugin_message(self._identifier, dict(type="grbl_state",
                                                                                mode=self.grblMode,
                                                                                state=self.grblState,
                                                                                x=self.grblX,
                                                                                y=self.grblY,
                                                                                z=self.grblZ,
                                                                                a=self.grblA,
                                                                                b=self.grblB,
                                                                                speed=self.grblSpeed,
                                                                                power=self.grblPowerLevel,
                                                                                positioning=self.positioning,
                                                                                feedmod=self.feedRate,
                                                                                rtcm=self.RTCM,
                                                                                depthlimit=self.cut_depth
                                                                                ))
                self.timeRef = currentTime
                # Send to gcode_ripper as well
                self._plugin_manager.send_plugin_message("gcode_ripper", dict(type="grbl_state",z=self.grblZ))


        # we only want to track requests we care about
        if cmd.upper() in self.trackedCmds:
            self.lastRequest.append(cmd)

        return (cmd, )


    # #-- gcode received hook 
    def hook_gcode_received(self, comm_instance, line, *args, **kwargs):
        self._logger.debug("__init__: hook_gcode_received line=[{}]".format(line.replace("\r", "<cr>").replace("\n", "<lf>")))

        # let's only do stuff if our profile is selected
        if self._printer_profile_manager.get_current_or_default()["id"] != "_bgs":
            return None

        # look for a status message
        if 'MPos' in line or 'WPos' in line:
            return _bgs.process_grbl_status_msg(self, line)
        
        if '[G5' in line:
            match = re.search(r'\[G(\d\.):(-?[\d\.]+),(-?[\d\.]+),(-?[\d\.]+)', line)
            if match:
                refframe = float(match.groups(1)[0])
                offsetx = float(match.groups(1)[1])
                offsety = float(match.groups(1)[2])
                offsetz = float(match.groups(1)[3])
                self.offsets.append({"frame" : "G{}", "x_offset" : offsetx, "y_offset" : offsety, "z_offset" : offsetz}.format(refframe))
        # look for an alarm
        if line.lower().startswith('alarm:'):
            return _bgs.process_grbl_alarm(self, line)

        # look for an error
        if not self.ignoreErrors and line.lower().startswith('error:'):
            return _bgs.process_grbl_error(self, line)
            
        if line.startswith('Grbl'):
            # it all starts here
            return "ok " + line

        if "PRB:" in line.upper():
            return line
         
        # forward any messages to the action notification plugin
        if "MSG:" in line.upper():
            ignoreList = ("[MSG:'$H'|'$X' to unlock]", "[MSG:INFO: '$H'|'$X' to unlock]")
            if not line.rstrip("\r").rstrip("\n").strip() in ignoreList:
                # auto reset
                if "reset to continue" in line.lower():
                    # automatically perform a soft reset if GRBL says we need one
                    self._printer.commands("M999")
                else:
                    # replace MSG: Disabled / Enabled with check mode info
                    line = line.replace("MSG:Disabled", "Check Mode Disabled")
                    line = line.replace("MSG:Enabled", "Check Mode Enabled")
                    # general clean up of the message
                    line = line.replace("[","").replace("]","").replace("MSG:","")
                    line = line.replace("\n", "").replace("\r", "")

                    if len(line) > 0:
                        _bgs.add_notifications(self, [line])
            return 

        # add to our lastResponse if this is not an acknowledgment
        if not "ok" in line.lower() and len(self.lastRequest) > 0:
            lastResponse = line.rstrip().rstrip("\r").rstrip("\n")
            self.lastResponse = self.lastResponse + lastResponse + "\n" 

        # $G response
        if line.startswith("[GC:"):
            _bgs.process_parser_status_msg(self, line)
            return 

        # grbl settings
        if line.lstrip().startswith("$"):
            match = re.search(r'^[$](-?[\d\.]+)=(-?[\d\.]+)', line)

            if not match is None:
                settingsId = int(match.groups(1)[0])
                settingsValue = match.groups(1)[1]

                self.grblSettings.update({settingsId: [settingsValue, self.grblSettingsNames.get(settingsId)]})
                self._logger.debug("setting id=[{}] value=[{}] description=[{}]".format(settingsId, settingsValue, self.grblSettingsNames.get(settingsId)))

                return line

        if not line.lstrip().lower().startswith("ok"):
            return

        # I've never seen these
        # if line.startswith('{'):
        #      # Regular ACKs
        #      # {0/0}ok
        #      # {5/16}ok
        #     return 'ok '
        # elif '{' in line:
        #      # Ack with return data
        #      # F300S1000{0/0}ok
        #     (before, _, _) = line.partition('{')
        #     return 'ok ' + before
        # else:

        # all that is left is an acknowledgement
        lastResponse = self.lastResponse.lstrip("\r").lstrip("\n").rstrip("\r").rstrip("\n")

        if len(self.lastRequest) > 0 and len(lastResponse) > 0:
            self.lastResponse = ""
            lastRequest = self.lastRequest[0]
            self.lastRequest.pop(0)
            self._logger.debug("tracked cmd: [{}] result: [{}]".format(lastRequest, lastResponse))

            # fluidnc config downloaded
            if lastRequest.upper() in ("$CD", "$CONFIG/DUMP"):
                self.fluidConfig = lastResponse
                self.fluidYaml = yaml.safe_load(lastResponse)
                self._settings.set(["fluidYaml"], yaml.dump(self.fluidYaml, sort_keys=False).replace(": null", ": "))
                self._settings.set_boolean(["laserMode"], _bgs.is_laser_mode(self))
                self._settings.save(trigger_event=True)
                # lets populate our x,y,z limits (namely set distance)
                _bgs.get_axes_limits(self)
                # retreive the fluid settings out of config yaml 
                self._printer.commands("$S")

            # grbl settings received
            if lastRequest.upper() in ("$$", "$+", "M115"): 
                self.grblConfig = lastResponse.split("\n")
                self._settings.set(["grblSettingsText"], _bgs.save_grbl_settings(self))
                self._settings.set_boolean(["laserMode"], _bgs.is_laser_mode(self))
                # lets populate our x,y,z limits (namely set distance)
                if all(id in self.grblSettings for id in (130, 131, 132)):
                    _bgs.get_axes_limits(self)

            # grbl version signatures
            if lastRequest.upper() in ("$I", "$BUILD/INFO"):
                self.grblVersion = lastResponse.replace("\n", " ").replace("\r", "")
                self._settings.set(["grblVersion"], self.grblVersion)
                self._settings.save(trigger_event=True)
                # trigger a fluidnc config download if fluid is detected
                if self.fluidConfig is None and _bgs.is_grbl_fluidnc(self):
                    self._printer.commands("$CD")

            # fluid settings outside of config yaml
            if lastRequest.upper() in ("$S", "$SETTINGS/LIST"):
                self.fluidSettings = json.loads("{" + lastResponse.replace("\r", "").replace("=", '": "').replace("\n", '", ').replace("$", '"').replace("\\", "\\\\") + '"}')
                self._settings.set(["fluidSettings"], self.fluidSettings)
                self._settings.save(trigger_event=True)
        return "ok "


    # ~ SimpleApiPlugin
    def on_api_get(self, request):
        return "this space intentionally left blank (for now)\n"

    def get_api_commands(self):
        self._logger.debug("__init__: get_api_commands")

        return dict(
            sleep=[],
            reset=[],
            unlock=[],
            homing=[],
            toggleWeak=[],
            getNotifications=[],
            clearNotifications=[],
            backupGrblSettings=[],
            restoreGrblSettings=[],
            origin=["origin_axis"],
            move=["sessionId", "direction", "distance", "axis"],
            updateGrblSetting=["id", "value"],
            feedRate=["feed_rate"],
            plungeRate=["plunge_rate"],
            powerRate=["power_rate"],
            cncrun=[],
            laserrun=[],
        )

    def on_api_command(self, command, data):
        self._logger.debug("__init__: on_api_command data=[{}]".format(data))

        # get our max rates and limits, any extra axes
        xf, yf, zf = _bgs.get_axes_max_rates(self)
        xl, yl, zl = _bgs.get_axes_limits(self)
        hasA = self._settings.get(["hasA"])
        hasB = self._settings.get(["hasB"])
        extra_axes = ""
        if hasA:
            extra_axes = extra_axes+"A0 "
        if hasB:
            extra_axes = extra_axes+"B0"

        if command == "sleep":
            self._printer.commands("$SLP")
            return

        if command == "unlock":
            if self.doSmoothie:
                self._printer.commands("M999")
            else:
                self._printer.commands("$X")
            return

        if command == "reset":
            # force a fake ack in case something is holding up the send queue
            # self._printer.fake_ack()
            self._printer.commands("M999", force=True)
            return

        if command == "updateGrblSetting":
            self._printer.commands("${}={}".format(data.get("id"), data.get("value")))
            self.grblSettings.update({int(data.get("id")): [data.get("value"), self.grblSettingsNames.get(int(data.get("id")))]})
            # self._printer.commands("$$")
            return

        if command == "backupGrblSettings":
            self._settings.set(["grblSettingsBackup"], _bgs.save_grbl_settings(self))
            self._settings.save()
            return

        if command == "restoreGrblSettings":
            settings = self._settings.get(["grblSettingsBackup"])

            if settings is None or len(settings) == 0:
                return

            for setting in settings.split("||"):
                if len(setting) > 0:
                    set = setting.split("|")
                    # self._logger.info("restoreGrblSettings: {}".format(set))
                    command = "${}={}".format(set[0], set[1])
                    self._printer.commands(command)

            time.sleep(1)
            return flask.jsonify({'res' : settings})

        if command == "homing" and self._printer.is_ready() and self.grblState in ("Idle", "Alarm"):
            self._printer.commands("$H")
            return

        if command == "feedRate":
            feedRate = float(data.get("feed_rate"))
            if not feedRate in (0, 100):
                self.feedRate = feedRate * .01
                # sending our current feedrate ensures grbl uses the new feedrate
                # now rather than wait for it to be sent -- it could be a while for
                # one to come in
                if self._printer.is_printing():
                    self._printer.commands("F{}".format(self.grblSpeed), force=True)
            else:
                self.feedRate = float(0)

            self._logger.info("feed rate overriden by %.0f%%", feedRate)
            return

        if command == "plungeRate":
            plungeRate = float(data.get("plunge_rate"))
            if not plungeRate in (0, 100):
                self.plungeRate = plungeRate * .01
            else:
                self.plungeRate = float(0)

            self._logger.info("plunge rate overriden by %.0f%%", plungeRate)
            return

        if command == "powerRate":
            powerRate = float(data.get("power_rate"))
            if not powerRate in (0, 100):
                self.powerRate = powerRate * .01
                # sending our current powerRate ensures grbl uses the new powerRate
                # now rather than wait for it to be sent -- it could be a while for
                # one to come in
                if self._printer.is_printing():
                    self._printer.commands("S{}".format(self.grblPowerLevel))

            else:
                self.powerRate = float(0)

            self._logger.info("power rate overriden by %.0f%%", powerRate)
            return

        if command == "getNotifications":
            return flask.jsonify(
                    notifications=[
                        {"timestamp": notification[0], "message": notification[1]}
                        for notification in self.notifications
                    ]
            )

        if command == "clearNotifications":
            self.notifications = []
            self._plugin_manager.send_plugin_message(self._identifier, dict(type="notification", message=""))
            return 

        # catch-all (TODO: should revisit state management) for validating printer State
        if not self._printer.is_ready() or not self.grblState in ("Idle", "Jog", "Check"):
            self._logger.debug("ignoring move related command - printer is not available")
            return

        if command == "move":
            sessionId = data.get("sessionId")
            # do move stuff
            direction = data.get("direction")
            distance = float(data.get("distance"))
            axis = data.get("axis")

            self._logger.debug("move direction=[{}] distance=[{}] axis=[{}] xlimit=[{}] ylimit=[{}] zlimit=[{}]".format(direction, distance, axis, xl, yl, zl))

            if direction == "home":
                if axis == "X":
                    self._printer.commands("G0 G90 X0")
                elif axis == "Y":
                    self._printer.commands("G0 G90 Y0")
                elif axis == "Z":
                    self._printer.commands("G0 G90 Z0")
                elif axis == "XZ":
                    self._printer.commands("G0 G90 X0 Z0")
                elif axis == "XZA":
                    self._printer.commands("G0 G90 X0 Z0 A0")
                elif axis == "A":
                    self._printer.commands("G0 G90 A0")
                elif axis == "B":
                    self._printer.commands("G0 G90 B0")
                else:
                    self._printer.commands("G0 G90 X0 Y0 Z0 {}".format(extra_axes))

                program = int(float(self.grblCoordinateSystem.replace("G", "")))
                program = -53 + program

                # add a notification if we just homed
                _bgs.add_notifications(self, ["Moved to coordinate system {} home for {}".format(program, axis)])
                return

            # check distance against limits
            if ("west" in direction or "east" in direction) and abs(distance) > abs(xl):
                return flask.jsonify({'res' : "Distance exceeds X axis limit"})
            if ("north" in direction or "south" in direction) and abs(distance) > abs(yl):
                return flask.jsonify({'res' : "Distance exceeds Y axis limit"})
            if ("up" in direction or "down" in direction) and abs(distance) > abs(zl):
                return flask.jsonify({'res' : "Distance exceeds Z axis limit"})

            if direction == "northwest":
                self._printer.commands("{}G91 G21 X{:f} Y{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance * -1 * self.invertX, distance * self.invertY, xf if xf < yf else yf))

            if direction == "north":
                self._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance * self.invertY, yf))

            if direction == "northeast":
                self._printer.commands("{}G91 G21 X{:f} Y{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance * self.invertX, distance * self.invertY, xf if xf < yf else yf))

            if direction == "west":
                self._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance * -1 * self.invertX, xf))

            if direction == "east":
                self._printer.commands("{}G91 G21 X{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance * self.invertX, xf))

            if direction == "southwest":
                #self._printer.commands("{}G91 G21 X{:f} Y{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance * -1 * self.invertX, distance * -1 * self.invertY, xf if xf < yf else yf))
                xval, zval = self.rot_trans_adjust(distance*-1)
                self._printer.commands("{}G91 G21 X{:f} Z{:f} B{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", xval * self.invertX, zval, distance*-1, zf)  )

            if direction == "south":
                self._printer.commands("{}G91 G21 Y{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance * -1 * self.invertY, yf))

            if direction == "southeast":
                xval, zval = self.rot_trans_adjust(distance)
                #self._printer.commands("{}G91 G21 X{:f} Y{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance * self.invertX, distance * -1 * self.invertY, xf if xf < yf else yf))
                self._printer.commands("{}G91 G21 X{:f} Z{:f} B{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", xval * self.invertX, zval, distance, zf)  )
            if direction == "up":
                self._printer.commands("{}G91 G21 Z{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance * self.invertZ, zf))

            if direction == "down":
                self._printer.commands("{}G91 G21 Z{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance * -1 * self.invertZ, zf))
            
            if direction == "a-right":
                self._printer.commands("{}G91 G21 A{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance, zf))
            
            if direction == "a-left":
                self._printer.commands("{}G91 G21 A{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance * -1, zf))
            
            if direction == "b-right":
                self._printer.commands("{}G91 G21 B{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance, zf))
            
            if direction == "b-left":
                self._printer.commands("{}G91 G21 B{:f} F{}".format("$J=" if _bgs.is_grbl_one_dot_one(self) else "G1 ", distance * -1, zf))

            return

        if command == "origin":
            axis = data.get("origin_axis")

            program = int(float(self.grblCoordinateSystem.replace("G", "")))
            program = -53 + program

            if axis == "X":
                self._printer.commands("G91 G10 P{} L20 X0".format(program))
            elif axis == "Y":
                self._printer.commands("G91 G10 P{} L20 Y0".format(program))
            elif axis == "Z":
                self._printer.commands("G91 G10 P{} L20 Z0".format(program))
            elif axis == "XZ":
                self._printer.commands("G91 G10 P{} L20 X0 Z0".format(program))
            elif axis == "XZA":
                self._printer.commands("G91 G10 P{} L20 X0 Z0 A0".format(program))
            elif axis == "A" and hasA:
                self._printer.commands("G91 G10 P{} L20 A0".format(program))
            elif axis == "B" and hasB:
                self._printer.commands("G91 G10 P{} L20 B0".format(program))
            elif axis == "A" and hasA:
                self._printer.commands("G91 G10 P{} L20 A0".format(program))
            elif axis == "B" and hasB:
                self._printer.commands("G91 G10 P{} L20 B0".format(program))
            else:
                self._printer.commands("G91 G10 P{0} L20 X0 Y0 Z0 {1}".format(program, extra_axes))

            _bgs.add_notifications(self, ["Coordinate system {} home for {} set".format(program, axis)])
            return

        if command == "toggleWeak":
            return flask.jsonify({'res' : _bgs.toggle_weak(self)})
        
        if command == "cncrun":
            self._logger.info(data)
            self.template = bool(data["template"])
            self.cut_depth = float(data["cut_depth"])
            self.track_plunge = bool(data["track_plunge"])
            self.minZ_th = float(data["minZ_th"])
            self.minZ_inc = float(data["minZ_inc"])
            self.do_ovality = bool(data["ovality"])
            self.ignore_moda = bool(data["ignore_moda"])
            #allow either positive or negative
            if self.cut_depth > 0:
                self.cut_depth = self.cut_depth * -1
            if self.minZ_th > 0:
                self.minZ_th = self.minZ_th * -1
            if self.minZ_inc < 0:
                self.minZ_inc = self.minZ_inc * -1
            if not self.template:
                self.cut_depth = "N/A"
            self.do_bangle = False
            self.do_mod_a = False
            self.do_mod_z = False
            self.TERMINATE = False
            self.queued_command = ""
            self.pauses_started = False
            self.RTCM = False
            self.queue_X = self.grblX
            self.queue_Z = self.grblZ
            self.queue_A = self.grblA
            self.queue_B = self.grblB
            self.queue_S = 0.0
            self.queue_F = 0.0
            return
        
        if command == "laserrun":
            self.template = bool(data["template"])
            self.cut_depth = float(data["cut_depth"])
            self.track_plunge = bool(data["track_plunge"])
            self.minZ_th = float(data["minZ_th"])
            self.minZ_inc = float(data["minZ_inc"])
            self.do_ovality = bool(data["ovality"])
            #allow either positive or negative
            if self.cut_depth > 0:
                self.cut_depth = self.cut_depth * -1
            if self.minZ_th > 0:
                self.minZ_th = self.minZ_th * -1
            if self.minZ_inc < 0:
                self.minZ_inc = self.minZ_inc * -1
            if not self.template:
                self.cut_depth = "N/A"
            self.do_bangle = False
            self.do_mod_a = False
            self.do_mod_z = False
            self.TERMINATE = False
            self.queued_command = ""
            self.pauses_started = False
            self.RTCM = False
            self.queue_X = self.grblX
            self.queue_Z = self.grblZ
            self.queue_A = self.grblA
            self.queue_B = self.grblB
            self.queue_S = 0.0
            self.queue_F = 0.0
            return

    def on_wizard_finish(self, handled):
        self._logger.debug("__init__: on_wizard_finish handled=[{}]".format(handled))
        if handled:
            self._settings.set(["wizard_version"], self.wizardVersion)
            self._settings.save()

    def is_wizard_required(self):
        requiredVersion = self.wizardVersion
        currentVersion = self._settings.get(["wizard_version"])
        self._logger.debug("__init__: is_wizard_required=[{}]".format(currentVersion is None or currentVersion != requiredVersion))
        return currentVersion is None or currentVersion != requiredVersion

    def get_wizard_version(self):
        self._logger.debug("__init__: get_wizard_version")
        return self.wizardVersion

    def get_wizard_details(self):
        self._logger.debug("__init__: get_wizard_details")
        return None


    # #~~ Softwareupdate hook
    def get_update_information(self):
        self._logger.debug("__init__: get_update_information")

        # Define the configuration for your plugin to use with the Software Update
        # Plugin here. See https://github.com/foosel/OctoPrint/wiki/Plugin:-Software-Update
        # for details.

        useDevChannel = self._settings.get_boolean(["useDevChannel"])
        checkout_folder = os.path.dirname(os.path.realpath(sys.executable))

        # dev channel check
        if useDevChannel:
            return dict(latheengraver=dict(
                displayName='LatheEngraver Support (Development Branch)',
                type='github_commit',
                user='paukstelis',
                repo='OctoPrint-LatheEngraver',
                branch="devel",
                current="fd0b1bac7a23ba4b01f58353c7a19c6bc4ea219e",
                method="pip",
                pip='https://github.com/paukstelis/Octoprint-LatheEngraver/archive/refs/heads/devel.zip',
                restart='octoprint'))
        else:
            return dict(latheengraver=dict(
                displayName='LatheEngraver Support',
                displayVersion=self._plugin_version,
                type='github_release',
                user='paukstelis',
                repo='OctoPrint-LatheEngraver',
                current=self._plugin_version,
                stable_branch={
                        "name": "Stable",
                        "branch": "main",
                        "commitish": ["main"],
                    },
                prerelease_branches=[
                        {
                            "name": "Release Candidate",
                            "branch": "rc",
                            "commitish": ["rc", "master"],
                        }
                    ],
                pip='https://github.com/paukstelis/OctoPrint-LatheEngraver/archive/{target_version}.zip'))


# If you want your plugin to be registered within OctoPrint under a different name than what you defined in setup.py
# ("OctoPrint-PluginSkeleton"), you may define that here. Same goes for the other metadata derived from setup.py that
# can be overwritten via __plugin_xyz__ control properties. See the documentation for that.

__plugin_name__ = 'LatheEngraver Support'
__plugin_pythoncompat__ = ">=2.7,<4"

def __plugin_load__():
    global __plugin_implementation__
    __plugin_implementation__ = LatheEngraverPlugin()

    global __plugin_hooks__
    __plugin_hooks__ = \
        {"octoprint.plugin.softwareupdate.check_config": __plugin_implementation__.get_update_information,
         "octoprint.comm.protocol.scripts": (__plugin_implementation__.hook_script_onresume, 1),
         "octoprint.comm.protocol.gcode.sending": __plugin_implementation__.hook_gcode_sending,
         "octoprint.comm.protocol.gcode.received": __plugin_implementation__.hook_gcode_received,
         "octoprint.comm.protocol.gcode.queuing": __plugin_implementation__.hook_gcode_queuing,
         "octoprint.filemanager.extension_tree": __plugin_implementation__.get_extension_tree}
