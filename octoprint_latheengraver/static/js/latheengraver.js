/*
 * View model for OctoPrint-Bettergrblsupport
 *
 * Author: Shell M. Shrader
 * License: Apache 2.0
 */
$(function() {
    function LatheengraverViewModel(parameters) {
        var self = this;

        self.sessionId = guid();

        self.settings = parameters[0];
        self.loginState = parameters[1];
        self.access = parameters[2];
        self.notifications = parameters[3];

        self.my_notifications = ko.observableArray();

        var $body = $('body');

        var $container = $('webcam_container');
        var controlPanel = $('#control_panel');
        var overridesPanel = $('#overrides_panel');

        self.webcamDisableTimeout = undefined;
        self.webcamLoaded = ko.observable(false);
        self.webcamMjpgEnabled = ko.observable(false);
        self.webcamHlsEnabled = ko.observable(false);
        self.webcamError = ko.observable(false);

        self.origin_axes = ko.observableArray(["Z", "X", "XZ","XZA","ALL"]);
        self.origin_axis = ko.observable("XZ");

        self.coordinate_systems = ko.observableArray(["G54", "G55", "G56", "G57", "G58", "G59"]);
        self.coordinate_system = ko.observable("G54");

        self.operator = ko.observable("=");
        self.distances = ko.observableArray([.1, 1, 5, 10, 60, 90]);
        self.distance = ko.observable(5);

        self.jogmove = false;

        self.is_printing = ko.observable(false);
        self.is_operational = ko.observable(false);
        self.isLoading = ko.observable(undefined);

        self.template = ko.observable(true);
        self.cut_depth = ko.observable(15.0);
        self.track_plunge = ko.observable(false);
        self.minZ = ko.observable(0);
        self.minZ_th = ko.observable(0);
        self.minZ_inc = ko.observable(0);
        self.ovality = ko.observable(false);
        self.ignore_moda = ko.observable(false);

        self.mode = ko.observable("N/A");
        self.state = ko.observable("N/A");
        self.xPos = ko.observable("N/A");
        self.yPos = ko.observable("N/A");
        self.zPos = ko.observable("N/A");
        self.aPos = ko.observable("N/A");
        self.bPos = ko.observable("N/A");
        self.power = ko.observable("N/A");
        self.speed = ko.observable("N/A");
        self.pins = ko.observable("N/A")
        self.positioning = ko.observable("N/A");
        self.rtcm = ko.observable("N/A");
        self.feedmod = ko.observable("N/A");
        self.depthlimit = ko.observable("N/A");

        self.feedRate = ko.observable(undefined);
        self.plungeRate = ko.observable(undefined);
        self.powerRate = ko.observable(undefined);

        self.controls = ko.observableArray([]);

        tab = document.getElementById("tab_plugin_latheengraver_link");
        tab.innerHTML = tab.innerHTML.replaceAll("LatheEngraver Support", "Control");
        
        self._disableWebcam = function() {
            // only disable webcam stream if tab is out of focus for more than 5s, otherwise we might cause
            // more load by the constant connection creation than by the actual webcam stream

            // safari bug doesn't release the mjpeg stream, so we just disable this for safari.
            if (OctoPrint.coreui.browser.safari) {
                return;
            }

            var timeout = self.settings.webcam_streamTimeout() || 5;
            self.webcamDisableTimeout = setTimeout(function() {
                console.log("Unloading webcam stream");
                $("#webcam_image").attr("src", "");
                self.webcamLoaded(false);
            }, timeout * 1000);
        };

        self._enableWebcam = function() {
            if (OctoPrint.coreui.selectedTab != undefined &&
                (OctoPrint.coreui.selectedTab != "#tab_plugin_latheengraver" ||
                    !OctoPrint.coreui.browserTabVisible)
            ) {
                return;
            }

            if (self.webcamDisableTimeout != undefined) {
                clearTimeout(self.webcamDisableTimeout);
            }

            // IF disabled then we dont need to do anything
            if (self.settings.webcam_webcamEnabled() == false) {
                return;
            }

            // Determine stream type and switch to corresponding webcam.
            var streamType = determineWebcamStreamType(self.settings.webcam_streamUrl());
            if (streamType == "mjpg") {
                self._switchToMjpgWebcam();
            } else if (streamType == "hls") {
                self._switchToHlsWebcam();
            } else {
                throw "Unknown stream type " + streamType;
            }
        };

        self.onWebcamLoaded = function() {
            if (self.webcamLoaded()) return;
            self.webcamLoaded(true);
            self.webcamError(false);
        };

        self.onWebcamErrored = function() {
            console.log("Webcam stream failed to load/disabled");
            if (self.webcamLoaded()) {
              self._enableWebcam();
              return;
            }
            self.webcamLoaded(false);
            self.webcamError(true);
        };

        self.onTabChange = function(current, previous) {
            if (current == "#tab_plugin_latheengraver") {
                self._enableWebcam();
            } else if (previous == "#tab_plugin_latheengraver") {
                self._disableWebcam();
            }
        };
        
        self.onBeforePrintStart = function(start_print_command) {
            var laserMode = self.settings.settings.plugins.latheengraver.laserMode();
            if (laserMode == true) {
                showDialog("#laserStartDialog", function(dialog){
                    OctoPrint.simpleApiCommand("latheengraver", "laserrun", { "sessionId": self.sessionId,
                        "direction": direction,
                        "distance": distance,
                        "axis": self.origin_axis() })
                    .done(function(response) {
                            console.log("Command succeeded:", response);
                            dialog.modal('hide');
                            start_print_command();
                        })
                });
            } else {
                showDialog("#cncStartDialog", function(dialog){
                    OctoPrint.simpleApiCommand("latheengraver", "cncrun", { "sessionId": self.sessionId,
                        "template": self.template(),
                        "cut_depth": self.cut_depth(),
                        "track_plunge": self.track_plunge(),
                        "minZ_th": self.minZ_th(),
                        "minZ_inc": self.minZ_inc(),
                        "ovality": self.ovality(),
                        "ignore_moda": self.ignore_moda()})
                    .done(function(response) {
                        console.log("Command succeeded:", response);
                        dialog.modal('hide');
                        start_print_command();
                    })
                    
                });
            }

            return false;
        };

        function showDialog(dialogId, confirmFunction){
            var myDialog = $(dialogId);
            var confirmButton = $("button.btn-confirm", myDialog);
            var cancelButton = $("button.btn-cancel", myDialog);
            //var dialogTitle = $("h3.modal-title", editDialog);
    
            confirmButton.unbind("click");
            confirmButton.bind("click", function() {
                //alert ("Do something");
                confirmFunction(myDialog);
            });
            myDialog.modal({
                //minHeight: function() { return Math.max($.fn.modal.defaults.maxHeight() - 80, 250); }
            }).css({
                width: 'auto',
                'margin-left': function() { return -($(this).width() /2); }
            });
        }

        self.onBrowserTabVisibilityChange = function(status) {
            if (status) {
                self._enableWebcam();
            } else {
                self._disableWebcam();
            }
        };

        self.webcamRatioClass = ko.pureComputed(function() {
            if (self.settings.webcam_streamRatio() == "4:3") {
                return "ratio43";
            } else {
                return "ratio169";
            }
        });

        self._switchToMjpgWebcam = function() {
            var webcamImage = $("#webcam_image");
            var currentSrc = webcamImage.attr("src");

            // safari bug doesn't release the mjpeg stream, so we just set it up the once
            if (OctoPrint.coreui.browser.safari && currentSrc != undefined) {
                return;
            }

            var newSrc = self.settings.webcam_streamUrl();
            if (currentSrc != newSrc) {
                if (self.settings.webcam_cacheBuster()) {
                    if (newSrc.lastIndexOf("?") > -1) {
                        newSrc += "&";
                    } else {
                        newSrc += "?";
                    }
                    newSrc += new Date().getTime();
                }

                self.webcamLoaded(false);
                self.webcamError(false);
                webcamImage.attr("src", newSrc);

                self.webcamHlsEnabled(false);
                self.webcamMjpgEnabled(true);
            }
        };

        self._switchToHlsWebcam = function() {
            var video = document.getElementById("webcam_hls");

            // Check for native playback options: https://developer.mozilla.org/en-US/docs/Web/API/HTMLMediaElement/canPlayType
            if (
                video != null &&
                typeof video.canPlayType != undefined &&
                video.canPlayType("application/vnd.apple.mpegurl") == "probably"
            ) {
                video.src = self.settings.webcam_streamUrl();
            } else if (Hls.isSupported()) {
                var hls = new Hls();
                hls.loadSource(self.settings.webcam_streamUrl());
                hls.attachMedia(video);
            }

            self.webcamMjpgEnabled(false);
            self.webcamHlsEnabled(true);
        };

        self.handleFocus = function (event, type, item) {
          window.setTimeout(function () {
              event.target.select();
          }, 0);
        };

        self.isIdleOrJogging = function() {
          return self.is_operational() &&
                 !self.is_printing() &&
                 (self.state() == 'Idle' || self.state() == 'Jog');
        };

        var jogInterval = undefined;

        self.jog = function(direction) {
          self.cancelJog();

          if (self.operator() == "J") {
            jogInterval = setInterval(function() { self.moveHead(direction, 10) }, 10);
          } else {
            self.moveHead(direction);
          }
        };

        self.cancelJog = function() {
          if (jogInterval != undefined) {
            OctoPrint.control.sendGcode("CANCELJOG");
            clearInterval(jogInterval);
            jogInterval = undefined;
          }
        }

        self.toggleWeak = function() {
            OctoPrint.simpleApiCommand("latheengraver", "toggleWeak")
                .done(
                    function(data) {
                        var btn = document.getElementById("grblLaserButton");
                        btn.innerHTML = btn.innerHTML.replace(btn.innerText, data["res"]);
                    }
                )
                .fail(
                    function(data, status) {
                        new PNotify({
                            title: "Laser action failed!",
                            text: data.responseText,
                            hide: true,
                            buttons: {
                                sticker: false,
                                closer: true
                            },
                            type: "error"
                        })
                    }
                );
        };

        self.distanceClicked = function(distance) {

                self.distance(parseFloat(distance));
        };

        self.operatorClicked = function() {
            if (self.operator() == "+") {
                self.operator("-");
            } else {
                if (self.operator() == "-") {
                    self.operator("J");
                } else {
                    if (self.operator() == "=") {
                        self.operator("+");
                    } else {
                      if (self.operator() == "J") {
                        self.operator("=");
                      }
                    }
                }
            }

            if (self.operator == "J") {

            }
        };

        self.moveHead = function(direction, distance) {
            if (distance == undefined) distance = self.distance();
            OctoPrint.simpleApiCommand("latheengraver", "move", { "sessionId": self.sessionId,
                                                                      "direction": direction,
                                                                      "distance": distance,
                                                                      "axis": self.origin_axis() })
                .done(
                    function(data) {
                        if (data != undefined && data["res"] != undefined && data["res"].length > 0) {
                            new PNotify({
                                title: "Unable to Move!",
                                text: data["res"],
                                hide: true,
                                buttons: {
                                    sticker: false,
                                    closer: true
                                },
                                type: "error"
                            });
                        }
                    })
                .fail(
                    function(data, status) {
                        new PNotify({
                            title: "Move Head failed!",
                            text: data.responseText,
                            hide: true,
                            buttons: {
                                sticker: false,
                                closer: true
                            },
                            type: "error"
                        });
                    })
        };

        self.sendCommand = function(command) {
            if (command == "unlock") {
                new PNotify({
                    title: "Unlock Machine",
                    text: "GRBL prefers you re-home your machine rather than unlock it.  Are you sure you want to unlock your machine?",
                    type: "notice",
                    hide: false,
                    animation: "fade",
                    animateSpeed: "slow",
                    sticker: false,
                    closer: true,
                    confirm: {
                        confirm: true,
                        buttons: [{
                                text: "CONFIRM",
                                click: function(notice) {
                                    OctoPrint.simpleApiCommand("latheengraver", command)
                                        .fail(
                                            function(data, status) {
                                                new PNotify({
                                                    title: "Unable to unlock machine!",
                                                    text: data.responseText,
                                                    hide: true,
                                                    buttons: {
                                                        sticker: false,
                                                        closer: true
                                                    },
                                                    type: "error"
                                                });
                                            });
                                    notice.remove();
                                }
                            },
                            {
                                text: "CANCEL",
                                click: function(notice) {
                                    notice.remove();
                                }
                            },
                        ]
                    },
                });
                return;
            }

            OctoPrint.simpleApiCommand("latheengraver", command, { "origin_axis": self.origin_axis(),
                                                                       "feed_rate": self.feedRate(),
                                                                       "plunge_rate": self.plungeRate(),
                                                                       "power_rate": self.powerRate() })
                .done(
                    function(data) {
                        if (command == "feedRate") self.feedRate(undefined);
                        if (command == "plungeRate") self.plungeRate(undefined);
                        if (command == "powerRate") self.powerRate(undefined);    
                    })
                .fail(
                    function(data, status) {
                        new PNotify({
                            title: "Unable to send command: " + command,
                            text: data.responseText,
                            hide: true,
                            buttons: {
                                sticker: false,
                                closer: true
                            },
                            type: "error"
                        });
                    });
        };
        
        self.replacePrint = function() {
            $("#files_template_machinecode").text(function () {
				var return_value = $(this).text();
				return_value = return_value.replace('Load and Print', 'Load and Start');
				return return_value;
			});
        }

        $("#track_plunge").on("change", function() {
            console.log(this.val());
        });

        self.runOptions = function() {
            var options = $("#run_options");

        }

        self.onBeforeBinding = function() {
            self.is_printing(self.settings.settings.plugins.latheengraver.is_printing());
            self.is_operational(self.settings.settings.plugins.latheengraver.is_operational());

            self.distance(self.settings.settings.plugins.latheengraver.control_distance());
            self.settings.settings.plugins.latheengraver.control_distance.subscribe(function(newValue) {
                self.distance(newValue);
            });
            //Replace Load and Print with Load and Start
            self.replacePrint();

            if (self.settings.settings.plugins.latheengraver.hasA() == true) { self.origin_axes.push("A"); }
            if (self.settings.settings.plugins.latheengraver.hasB() == true) { self.origin_axes.push("B"); }
            if (self.settings.settings.plugins.latheengraver.laserMode() == true) { $(".laserbtn").show(); }
            if (self.settings.settings.plugins.latheengraver.laserMode() == false) { $(".laserbtn").hide(); }
    
            self.notifications.requestData = self.overrideRequestData;
            self.notifications.clear = self.overrideClear;
            self.notifications.onDataUpdaterPluginMessage = self.overrideOnDataUpdaterPluginMessage;

        };

        self.overrideRequestData = function() {
            OctoPrint.simpleApiCommand("latheengraver", "getNotifications").done(self.notifications.fromResponse);
        };

        self.overrideClear = function() {
            OctoPrint.simpleApiCommand("latheengraver", "clearNotifications");    
        };

        self.overrideOnDataUpdaterPluginMessage = function(plugin, data) {
            if (plugin !== "action_command_notification") {
                return;
            }

            self.notifications.requestData();

            if (data.message) {
                if (self.settings.settings.plugins.action_command_notification.enable_popups()) {
                    new PNotify({
                        title: gettext("Machine Notification"),
                        text: data.message,
                        hide: false,
                        icon: "fa fa-bell-o",
                        buttons: {
                            sticker: false,
                            closer: true
                        }
                    });
                }
            }
        };

        self.coordinateSystemChanged = function (coordinate_system) {
          // self.coordinate_system(coordinate_system)
            OctoPrint.control.sendGcode([coordinate_system, "?"]);
        };

        self.onAllBound = function (allViewModels) {
          self._enableWebcam();

          OctoPrint.control.getCustomControls().done(function (response) {
            self.controls(self._processControls(response.controls));
          });
        };

        self.fromCurrentData = function(data) {
            self._processStateData(data.state);
        };

        self.fromHistoryData = function(data) {
            self._processStateData(data.state);
        };

        self._processStateData = function(data) {
            self.is_printing(data.flags.printing);
            self.is_operational(data.flags.operational);
            self.isLoading(data.flags.loading);

            if (self.is_printing()) {
              self.state("Run");
            }

            if (!self.is_operational()) {
              self.state("N/A");
            }
        };

        self.onDataUpdaterPluginMessage = function(plugin, data) {
            if (plugin == 'latheengraver' && data.type == 'grbl_state') {
                if (data.mode != undefined) self.mode(data.mode);

                if (data.state != undefined && !(self.is_printing() && data.state == "Idle")) {
                  self.state(data.state);
                }

                if (data.x != undefined) self.xPos(Number.parseFloat(data.x).toFixed(2));
                if (data.y != undefined) self.yPos(Number.parseFloat(data.y).toFixed(2));
                if (data.z != undefined) self.zPos(Number.parseFloat(data.z).toFixed(2));
                if (data.a != undefined) self.aPos(Number.parseFloat(data.a).toFixed(2));
                if (data.b != undefined) self.bPos(Number.parseFloat(data.b).toFixed(2));

                if (data.speed != undefined) self.speed(Number.parseFloat(data.speed).toFixed(2));
                if (data.pins != undefined) self.pins(data.pins);

                if (data.power != undefined) {
                  var newPower = Number.parseFloat(data.power);
                  if (data.state != "Run" && data.power != "N/A" && !self.is_printing()) {
                    var btn = document.getElementById("grblLaserButton");
                    var oldPower = Number.parseFloat(self.power);

                    if (btn != null) {
                        if (newPower == 0 && oldPower != 0) {
                            btn.innerHTML = btn.innerHTML.replace(btn.innerText, "Weak Laser");
                        } else {
                            if (oldPower == 0 && newPower != 0) {
                                btn.innerHTML = btn.innerHTML.replace(btn.innerText, "Laser Off");
                            }
                        }
                    }
                  }
                  self.power(newPower.toFixed(2));
                }

                if (data.coord != undefined) self.coordinate_system(data.coord);
                if (data.feedmod != undefined) self.feedmod(data.feedmod);
                if (data.rtcm != undefined) self.rtcm(data.rtcm);
                if (data.depthlimit != undefined) self.depthlimit(data.depthlimit); 
                if (data.positioning != undefined) {
                  if (data.positioning == 0) {
                    self.positioning("Absolute");
                  } else {
                    self.positioning("Relative");
                  }
                }
                // console.log("mode=" + data.mode + " state=" + data.state + " x=" + data.x + " y=" + data.y + " z=" + data.z + " power=" + data.power + " speed=" + data.speed);
                return
            }

            if (plugin == 'latheengraver' && data.type == 'laserchange') {
                console.log(data);
                if (data.laser == "true") {
                    $(".laserbtn").show();
                } else {
                    $(".laserbtn").hide();
                }
            }

            if (plugin == 'latheengraver' && data.type == 'simple_notify') {
                if (data.sessionId == undefined || data.sessionId == self.sessionId) {
                    new PNotify({
                        title: data.title,
                        text: data.text,
                        hide: data.hide,
                        animation: "fade",
                        animateSpeed: "slow",
                        mouseReset: true,
                        delay: data.delay,
                        buttons: {
                            sticker: true,
                            closer: true
                        },
                        type: data.notify_type,
                    });
                }
                return
            }

            if (plugin == 'latheengraver' && data.type == 'restart_required') {
                new PNotify({
                    title: "Restart Required",
                    text: "Octoprint may need to be restarted for your changes to take full effect.",
                    hide: false,
                    animation: "fade",
                    animateSpeed: "slow",
                    mouseReset: true,
                    buttons: {
                        sticker: true,
                        closer: true
                    },
                    type: "notice"
                });
                return
            }

            if (plugin == "latheengraver" && data.type == "notification") {
                self.notifications.onDataUpdaterPluginMessage("action_command_notification", {message: data.message})                    
            }
        }

        self.modeClick = function() {
          if (self.is_operational() && !self.is_printing()) {
            if (self.mode() == "WPos") {
            //changes for grblhal
              OctoPrint.control.sendGcode(["$10=157", "?", "$$"]);
            } else {
              OctoPrint.control.sendGcode(["$10=156", "?", "$$"]);
            }
          }
        }

        self.moveClick = function() {
          if (self.is_operational() && !self.is_printing() && self.state() == "Idle") {
            if (self.positioning() == "Absolute") {
              OctoPrint.control.sendGcode(["G91"]);
            } else {
              OctoPrint.control.sendGcode(["G90"]);
            }
          }
        }

        self.coolClick = function() {
          if (self.is_operational()) {
            if (self.coolant() == "Off") {
              OctoPrint.control.sendGcode(["M8"]);
            } else {
              OctoPrint.control.sendGcode(["M9"]);
            }
          }
        }

        self.fsClick = function() {  
            $body.toggleClass('inlineFullscreen');
            $container.toggleClass("inline fullscreen");
            // streamImg.classList.toggle("fullscreen");

            var progressBar = document.getElementById("state");

            if (progressBar.style.visibility == "" || progressBar.style.visibility == "visible") {
                progressBar.style.visibility = "hidden";
            } else {
                progressBar.style.visibility = "visible";
            }

            if (controlPanel.is(':visible')) {
                controlPanel.hide();
            } else {
                controlPanel.show();
            }

            if (overridesPanel.is(':visible')) {
                overridesPanel.hide();
            } else {
                overridesPanel.show();
            }

            $('#sidebar_plugin_latheengraver_wrapper').toggle();
            $('#sidebar_plugin_action_command_notification_wrapper').toggle();
        }


        self.feedRateResetter = ko.observable();
        self.resetFeedRateDisplay = function() {
            self.cancelFeedRateDisplayReset();
            self.feedRateResetter(
                setTimeout(function() {
                    self.feedRate(undefined);
                    self.feedRateResetter(undefined);
                }, 5000)
            );
        };
        self.cancelFeedRateDisplayReset = function() {
            var resetter = self.feedRateResetter();
            if (resetter) {
                clearTimeout(resetter);
                self.feedRateResetter(undefined);
            }
        };

        self.plungeRateResetter = ko.observable();
        self.resetPlungeRateDisplay = function() {
            self.cancelPlungeRateDisplayReset();
            self.plungeRateResetter(
                setTimeout(function() {
                    self.plungeRate(undefined);
                    self.plungeRateResetter(undefined);
                }, 5000)
            );
        };
        self.cancelPlungeRateDisplayReset = function() {
            var resetter = self.plungeRateResetter();
            if (resetter) {
                clearTimeout(resetter);
                self.plungeRateResetter(undefined);
            }
        };

        self.powerRateResetter = ko.observable();
        self.resetPowerRateDisplay = function() {
            self.cancelPowerRateDisplayReset();
            self.powerRateResetter(
                setTimeout(function() {
                    self.powerRate(undefined);
                    self.powerRateResetter(undefined);
                }, 5000)
            );
        };
        self.cancelPowerRateDisplayReset = function() {
            var resetter = self.powerRateResetter();
            if (resetter) {
                clearTimeout(resetter);
                self.powerRateResetter(undefined);
            }
        };

        self._processControls = function (controls) {
            for (var i = 0; i < controls.length; i++) {
                controls[i] = self._processControl(controls[i]);
            }
            return controls;
        };

        self._processControl = function (control) {
            if (control.hasOwnProperty("processed") && control.processed) {
                return control;
            }

            if (
                control.hasOwnProperty("template") &&
                control.hasOwnProperty("key") &&
                control.hasOwnProperty("template_key") &&
                !control.hasOwnProperty("output")
            ) {
                control.output = ko.observable(control.default || "");
                if (!self.feedbackControlLookup.hasOwnProperty(control.key)) {
                    self.feedbackControlLookup[control.key] = {};
                }
                self.feedbackControlLookup[control.key][control.template_key] =
                    control.output;
            }

            if (control.hasOwnProperty("children")) {
                control.children = ko.observableArray(
                    self._processControls(control.children)
                );
                if (
                    !control.hasOwnProperty("layout") ||
                    !(
                        control.layout == "vertical" ||
                        control.layout == "horizontal" ||
                        control.layout == "horizontal_grid"
                    )
                ) {
                    control.layout = "vertical";
                }

                if (!control.hasOwnProperty("collapsed")) {
                    control.collapsed = false;
                }
            }

            if (control.hasOwnProperty("input")) {
                var attributeToInt = function (obj, key, def) {
                    if (obj.hasOwnProperty(key)) {
                        var val = obj[key];
                        if (_.isNumber(val)) {
                            return val;
                        }

                        var parsedVal = parseInt(val);
                        if (!isNaN(parsedVal)) {
                            return parsedVal;
                        }
                    }
                    return def;
                };

                _.each(control.input, function (element) {
                    if (element.hasOwnProperty("slider") && _.isObject(element.slider)) {
                        element.slider["min"] = attributeToInt(element.slider, "min", 0);
                        element.slider["max"] = attributeToInt(
                            element.slider,
                            "max",
                            255
                        );

                        // try defaultValue, default to min
                        var defaultValue = attributeToInt(
                            element,
                            "default",
                            element.slider.min
                        );

                        // if default value is not within range of min and max, correct that
                        if (
                            !_.inRange(
                                defaultValue,
                                element.slider.min,
                                element.slider.max
                            )
                        ) {
                            // use bound closer to configured default value
                            defaultValue =
                                defaultValue < element.slider.min
                                    ? element.slider.min
                                    : element.slider.max;
                        }

                        element.value = ko.observable(defaultValue);
                    } else {
                        element.slider = false;
                        element.value = ko.observable(
                            element.hasOwnProperty("default")
                                ? element["default"]
                                : undefined
                        );
                    }
                });
            }

            if (control.hasOwnProperty("javascript")) {
                var js = control.javascript;

                // if js is a function everything's fine already, but if it's a string we need to eval that first
                if (!_.isFunction(js)) {
                    control.javascript = function (data) {
                        eval(js);
                    };
                }
            }

            if (control.hasOwnProperty("enabled")) {
                var enabled = control.enabled;

                // if js is a function everything's fine already, but if it's a string we need to eval that first
                if (!_.isFunction(enabled)) {
                    control.enabled = function (data) {
                        return eval(enabled);
                    };
                }
            }

            if (!control.hasOwnProperty("additionalClasses")) {
                control.additionalClasses = "";
            }

            control.processed = true;
            return control;
        };


        self.isCustomEnabled = function (data) {
            if (data.hasOwnProperty("enabled")) {
                return data.enabled(data);
            } else {
                return (
                    self.loginState.hasPermission(self.access.permissions.CONTROL) &&
                    self.is_operational()
                );
            }
        };

        self.clickCustom = function (data) {
            var callback;
            if (data.hasOwnProperty("javascript")) {
                callback = data.javascript;
            } else {
                callback = self.sendCustomCommand;
            }

            if (data.confirm) {
                showConfirmationDialog({
                    message: data.confirm,
                    onproceed: function (e) {
                        callback(data);
                    }
                });
            } else {
                callback(data);
            }
        };

        self.sendCustomCommand = function (command) {
            if (!command) return;

            var parameters = {};
            if (command.hasOwnProperty("input")) {
                _.each(command.input, function (input) {
                    if (
                        !input.hasOwnProperty("parameter") ||
                        !input.hasOwnProperty("value")
                    ) {
                        return;
                    }

                    parameters[input.parameter] = input.value();
                });
            }

            if (command.hasOwnProperty("command") || command.hasOwnProperty("commands")) {
                var commands = command.commands || [command.command];
                OctoPrint.control.sendGcodeWithParameters(commands, parameters);
            } else if (command.hasOwnProperty("script")) {
                var script = command.script;
                var context = command.context || {};
                OctoPrint.control.sendGcodeScriptWithParameters(
                    script,
                    context,
                    parameters
                );
            }
        };


        self.displayMode = function (customControl) {
            if (customControl.hasOwnProperty("children")) {
                if (customControl.name) {
                    return "customControls_containerTemplate_collapsable";
                } else {
                    return "customControls_containerTemplate_nameless";
                }
            } else {
                return "customControls_controlTemplate";
            }
        };

        self.rowCss = function (customControl) {
            var span = "span2";
            var offset = "";
            if (customControl.hasOwnProperty("width")) {
                span = "span" + customControl.width;
            }
            if (customControl.hasOwnProperty("offset")) {
                offset = "offset" + customControl.offset;
            }
            return span + " " + offset;
        };

        self.monitor_jog = function() {
            if (self.jogmove == 1) {
                self.jogmove = 2;
            }
            if (self.jogmove == 0) {
                self.jogmove = 1;
            } 
        };

        self.onKeyDown = function (data, event) {
            if (!self.settings.feature_keyboardControl()) return;

            var button = undefined;
            var visualizeClick = true;
            var simulateTouch = false;

            switch (event.which) {
                case 37: // left arrow key
                    // X-
                    button = $("#control-west");
                    simulateTouch = true;
                    this.monitor_jog();
                    break;
                case 38: // up arrow key
                    // Y+
                    button = $("#control-zdown");
                    simulateTouch = false;
                    this.monitor_jog();
                    break;
                case 39: // right arrow key
                    // X+
                    button = $("#control-east");
                    simulateTouch = true;
                    this.monitor_jog();
                    break;
                case 40: // down arrow key
                    // Y-
                    button = $("#control-zup");
                    simulateTouch = false;
                    this.monitor_jog();
                    break;
                case 188: //, or <
                    button = $("#control-a-right");
                    simulateTouch = true;
                    this.monitor_jog();
                    break;
                case 190: //. or >
                    button = $("#control-a-left");
                    simulateTouch = true;
                    this.monitor_jog();
                    break;
                case 219: // [
                    button = $("#control-b-left");
                    simulateTouch = true;
                    this.monitor_jog();
                    break;
                case 221: // [
                    button = $("#control-b-right");
                    simulateTouch = true;
                    this.monitor_jog();
                    break;
                case 50: // number 2
                case 98: // numpad 2
                    // Distance 0.1
                    button = $("#control-distance-0");
                    break;
                case 51: // number 3
                case 99: // numpad 3
                    // Distance 1
                    button = $("#control-distance-1");
                    break;
                case 52: // number 4
                case 100: // numpad 4
                    // Distance 5
                    button = $("#control-distance-2");
                    break;
                case 53: // number 5
                case 101: // numpad 5
                    // Distance 10
                    button = $("#control-distance-3");
                    break;
                case 54: // number 6
                case 102: // numpad 6
                    // Distance 50
                    button = $("#control-distance-4");
                    break;
                case 55: // number 7
                case 103: // numpad 7
                    // Distance 100
                    button = $("#control-distance-5");
                    break;
                
                case 33: // page up key
                case 87: // w key
                    // z lift up
                   button = $("#control-zup");
                    break;
                case 34: // page down key
                case 83: // s key
                    // z lift down
                    button = $("#control-zdown");
                    break;
                case 36: // home key
                    // xy home
                    button = $("#control-home");
                    $("#control-axes-XY").click();
                    break;
                case 35: // end key
                    // z home
                    button = $("#control-home");
                    $("#control-axes-Z").click();
                    break;
                default:
                    event.preventDefault();
                    return false;
            }
            //console.log(button);
            if (button === undefined) {
                return false;
            } else {
                event.preventDefault();
                if (visualizeClick) {
                    button.addClass("active");
                    setTimeout(function () {
                        button.removeClass("active");
                    }, 150);
                }
                if (simulateTouch) {
                    button.mousedown();
                    setTimeout(function () {
                        button.mouseup();
                    }, 150);
                } else {
                    button.click();
                }
            }
        };

        $(document).ready(function() {
            $(this).keydown(function(e) {
                if (OctoPrint.coreui.selectedTab != undefined &&
                        OctoPrint.coreui.selectedTab == "#tab_plugin_latheengraver" &&
                        OctoPrint.coreui.browserTabVisible && $(":focus").length == 0) {
                    self.onKeyDown(undefined, e);
                    
                }
            });
        
            $(this).keyup(function(e) {
                if (self.jogmove == 2) {
                    //send jog stop character
                    OctoPrint.control.sendGcode("CANCELJOG");
                }
                self.jogmove = 0;
                // console.log("keyup");
            });
        });
    }

    // cute little hack for removing "Print" from the start button
    $('#job_print')[0].innerHTML = "<i class=\"fas\" data-bind=\"css: {'fa-print': !isPaused(), 'fa-undo': isPaused()}\"></i> <span data-bind=\"text: (isPaused() ? 'Restart' : 'Start')\">Start</span>"

    // cute hack for changing printer to machine for the action notify sidebar plugin
    var x = document.getElementById("sidebar_plugin_action_command_notification_wrapper");
    if (x != undefined) {
        x.outerHTML = x.outerHTML.replace("printer.", "machine.").replace("Printer ", "");
    }

    // cute hack for changing printer to machine for the connection sidebar plugin
    var y = document.getElementById("connection_wrapper");
    if (y != undefined) {
        y.outerHTML = y.outerHTML.replace("Printer ", "Machine ");
    }

    // cute hack for removing print from the state sidebar plugin
    var z = document.getElementById("state_wrapper");
    if (z != undefined) {
        z.innerHTML = z.innerHTML.replaceAll(">Print ", ">Job ");
        z.innerHTML = z.innerHTML.replaceAll(" print ", " ");
        z.innerHTML = z.innerHTML.replaceAll(" Print ", " ");
        z.innerHTML = z.innerHTML.replaceAll(">Printed", ">Bytes");
        z.innerHTML = z.innerHTML.replaceAll(" printed ", " streamed ");
    }

    // cute hack for removing Printer from the Settings Menu
    setTimeout(checkSettings, 100);
    function checkSettings() {
        var a = document.getElementById("UICsettingsMenu");
        if (a != undefined) {
            a.outerHTML = a.outerHTML.replaceAll("Printer ", "Machine ");
        } else {
            setTimeout(checkSettings, 100);
        }
    }


    function guid() {
        return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function(c) {
            var r = Math.random() * 16 | 0,
                v = c == 'x' ? r : (r & 0x3 | 0x8);
            return v.toString(16);
        });
    }

    var haveEvents = 'ongamepadconnected' in window;
    var controllers = {};
    var controllerInterval = undefined;

    function connecthandler(e) {
      addgamepad(e.gamepad);
    }

    function addgamepad(gamepad) {
      controllers[gamepad.index] = gamepad;
      if (controllerInterval == undefined) {
        console.log("updateStatus interval created");
        controllerInterval = setInterval(updateStatus, 250);
      }
    }

    function disconnecthandler(e) {
      removegamepad(e.gamepad);
    }

    function removegamepad(gamepad) {
      delete controllers[gamepad.index];

      var j;
      var empty = true;

      for (j in controllers) {
        if (j != undefined) {
          empty = false;
          break;
        }
      }

      if (empty) {
        console.log("updateStatus interval destroyed");
        clearInterval(controllerInterval);
        controllerInterval = undefined;

        var state = document.getElementById("bgs_printer_state").innerText;
        if (state != "Run") {
          OctoPrint.control.sendGcode("CANCELJOG");
        }
      }
    }

    function scaleValue(value, from, to) {
    	var scale = (to[1] - to[0]) / (from[1] - from[0]);
    	var capped = Math.min(from[1], Math.max(from[0], value)) - from[0];
    	return ~~(capped * scale + to[0]);
    }

    var lastX = 0;
    var lastY = 0;

    function sendkeydown(thekey, keyval, whichkey) {
        document.dispatchEvent(
            new KeyboardEvent("keydown", {
              key: thekey,
              keyCode: whichkey, // example values.
              code: "KeyE", // put everything you need in this object.
              which: whichkey,
              shiftKey: false, // you don't need to include values
              ctrlKey: false,  // if you aren't going to use them.
              metaKey: false   // these are here for example's sake.
            })
          );
    }

    function updateStatus() {
        var state = document.getElementById("bgs_printer_state").innerText;
        if (!(state == "Idle" || state == "Jog")) {
          return;
        }
  
        if (!haveEvents) {
          scangamepads();
        }
  
        var i = 0;
        var j;
  
        for (j in controllers) {
          var controller = controllers[j];
          var x = 0;
          var y = 0;

                  //Rotate A
                  if (controller.buttons[4]["pressed"] == true) {
                    //sendkeydown("Comma",188,188);
                    sendkeydown("Period",190,190);
                    controller.buttons[4]["pressed"] = false;
                  }

                  if (controller.buttons[5]["pressed"] == true) {
                    //sendkeydown("Period",190,190);
                    sendkeydown("Comma",188,188);
                    controller.buttons[5]["pressed"] = false;
                  }

                  if (controller.buttons[6]["pressed"] == true) {
                    sendkeydown("OB",219,219);
                    controller.buttons[6]["pressed"] = false;
                  }

                  if (controller.buttons[7]["pressed"] == true) {
                    sendkeydown("CB",221,221);
                    controller.buttons[7]["pressed"] = false;
                  }
                  //swapping Y and Z
                  if (controller.buttons[12]["pressed"] == true) {
                    //Z DOWN
                    sendkeydown("PgDn",34,34);
                    controller.buttons[12]["pressed"] = false;
                  }
                  if (controller.buttons[13]["pressed"] == true) {
                    //Z UP
                    sendkeydown("PgUp",33,33);
                    controller.buttons[13]["pressed"] = false;
                  }
                  if (controller.buttons[14]["pressed"] == true) {
                    //Z DOWN
                    //sendkeydown("Right",39,39);
                    sendkeydown("Left",37,37);
                    controller.buttons[14]["pressed"] = false;
                  }
                  if (controller.buttons[15]["pressed"] == true) {
                    //Z DOWN
                    //sendkeydown("Left",37,37);
                    sendkeydown("Right",39,39);
                    controller.buttons[15]["pressed"] = false;
                  }
                  //distances
                  if (controller.buttons[0]["pressed"] == true) {
                    //0.1
                    sendkeydown("NP0",98,98);
                    controller.buttons[0]["pressed"] = false;
                  }
                  if (controller.buttons[1]["pressed"] == true) {
                    //1
                    sendkeydown("NP1",99,99);
                    controller.buttons[1]["pressed"] = false;
                  }
                  if (controller.buttons[3]["pressed"] == true) {
                    //5
                    sendkeydown("NP2",100,100);
                    controller.buttons[3]["pressed"] = false;
                  }
                  if (controller.buttons[2]["pressed"] == true) {
                    //10
                    sendkeydown("NP3",101,101);
                    controller.buttons[2]["pressed"] = false;
                  }
          for (i = 0; i < 2; i++) {
            if (Math.abs(controller.axes[i]) >= .1) {
              value = controller.axes[i];
              // value = value + .2 * (value > 0 ? -1 : 1);
  
              if (i == 1 || i == 3) {
                invert = -1;
              } else {
                invert = 1;
              }
  
              value = value * 20 * invert;
  
              if (invert == -1) {
                y = value;
              } else {
                x = value;
              }
            } else {
              if (i == 1 || i == 3) {
                y = 0;
              } else {
                x = 0;
              }
            }
          }
        }
        if (x != lastX || y != lastY) {
          if (x == 0 && y == 0) {
            OctoPrint.control.sendGcode("CANCELJOG");
            console.log("gamepad centered");
          }
  
          lastX = x;
          lastY = y;
        }
  
        if (x != 0 || y != 0) {
          var fastAxis = 0;
  
          if (Math.abs(x) > Math.abs(y)) {
            fastAxis = Math.abs(x);
          } else {
            fastAxis = Math.abs(y);
          }
  
          OctoPrint.control.sendGcode("$J=G91 G21 X" + x + " Z" + y*-1 + " F" + scaleValue(fastAxis, [1,20], [100,600]));
          console.log("x=" + x + " z=" + y);
        }
      }

    function scangamepads() {
      var gamepads = navigator.getGamepads ? navigator.getGamepads() : (navigator.webkitGetGamepads ? navigator.webkitGetGamepads() : []);
      for (var i = 0; i < gamepads.length; i++) {
        if (gamepads[i]) {
          if (gamepads[i].index in controllers) {
            controllers[gamepads[i].index] = gamepads[i];
          } else {
            addgamepad(gamepads[i]);
          }
        }
      }
    }

    window.addEventListener("gamepadconnected", connecthandler);
    window.addEventListener("gamepaddisconnected", disconnecthandler);

    if (!haveEvents) {
     setInterval(scangamepads, 150);
    }

    OCTOPRINT_VIEWMODELS.push([
        LatheengraverViewModel,
        ["settingsViewModel", "loginStateViewModel", "accessViewModel", "actionCommandNotificationViewModel"],
        ["#tab_plugin_latheengraver"]
    ]);
});
